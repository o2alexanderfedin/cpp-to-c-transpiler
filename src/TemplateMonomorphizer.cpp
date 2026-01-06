/**
 * @file TemplateMonomorphizer.cpp
 * @brief Implementation of TemplateMonomorphizer class
 *
 * Story #68: Template Monomorphization and Code Generation
 * Phase 32.1: Refactored to AST-based generation (from string generation)
 *
 * Design Principles:
 * - SOLID: Single Responsibility (monomorphization only)
 * - KISS: Simple AST node creation using CNodeBuilder patterns
 * - DRY: Reuse CNodeBuilder methods instead of manual AST construction
 * - YAGNI: Only implement what's needed for template monomorphization
 */

#include "TemplateMonomorphizer.h"
#include "llvm/ADT/SmallString.h"
#include <sstream>

using namespace clang;

// ============================================================================
// Constructor
// ============================================================================

TemplateMonomorphizer::TemplateMonomorphizer(ASTContext& Context,
                                            CNodeBuilder& Builder)
    : Context(Context), Builder(Builder) {
}

// ============================================================================
// Public API: AST Generation Methods (Phase 32.1)
// ============================================================================

RecordDecl* TemplateMonomorphizer::monomorphizeClass(ClassTemplateSpecializationDecl* D) {
    if (!D) return nullptr;

    // Generate mangled name for this instantiation
    std::string mangledName = generateMangledName(
        D->getSpecializedTemplate()->getNameAsString(),
        D->getTemplateArgs()
    );

    // Create C struct using CNodeBuilder
    RecordDecl* CStruct = createStruct(D, mangledName);

    return CStruct;
}

std::vector<FunctionDecl*> TemplateMonomorphizer::monomorphizeClassMethods(
    ClassTemplateSpecializationDecl* D,
    RecordDecl* CStruct) {

    if (!D || !CStruct) return {};

    std::vector<FunctionDecl*> methods;
    std::string mangledName = CStruct->getNameAsString();

    // BUG FIX (Bug #16): For template specializations, methods aren't in decls().
    // We need to get them from the template definition (pattern).
    //
    // Root cause: ClassTemplateSpecializationDecl::decls() returns 0 items because
    // methods are defined in the template pattern, not duplicated in each instantiation.
    //
    // Solution: Get the template pattern via getSpecializedTemplate()->getTemplatedDecl()
    // and iterate over its methods, then monomorphize each one with the concrete types.

    ClassTemplateDecl* Template = D->getSpecializedTemplate();
    CXXRecordDecl* Pattern = Template ? Template->getTemplatedDecl() : nullptr;

    if (!Pattern) {
        return methods;
    }

    // Iterate over template pattern's methods and monomorphize each one
    for (auto* Method : Pattern->methods()) {
        // Skip compiler-generated methods
        if (Method->isImplicit()) continue;

        // Skip constructors and destructors (handled separately if needed)
        if (isa<CXXConstructorDecl>(Method) || isa<CXXDestructorDecl>(Method)) {
            continue;
        }

        FunctionDecl* CMethod = createMethodFunction(
            Method,
            mangledName,
            D->getTemplateArgs()
        );

        if (CMethod) {
            methods.push_back(CMethod);
        }
    }

    return methods;
}

FunctionDecl* TemplateMonomorphizer::monomorphizeFunction(FunctionDecl* D) {
    if (!D) return nullptr;

    // Get function template specialization info
    FunctionTemplateSpecializationInfo* FTSI = D->getTemplateSpecializationInfo();
    if (!FTSI) return nullptr;

    // Generate mangled function name with template arguments
    const TemplateArgumentList* TemplateArgs = FTSI->TemplateArguments;
    std::string mangledName = generateMangledName(
        D->getNameAsString(),
        *TemplateArgs
    );

    // Build parameter list
    llvm::SmallVector<ParmVarDecl*, 4> params;
    for (unsigned i = 0; i < D->getNumParams(); ++i) {
        ParmVarDecl* OrigParam = D->getParamDecl(i);

        // Types are already substituted by Clang during instantiation
        QualType paramType = OrigParam->getType();
        std::string paramName = OrigParam->getNameAsString();

        // BUG FIX: Convert C++ types to C types
        paramType = convertToCType(paramType);

        // Create C parameter using CNodeBuilder
        ParmVarDecl* CParam = Builder.param(paramType, paramName);
        params.push_back(CParam);
    }

    // Return type (already substituted by Clang)
    QualType returnType = D->getReturnType();

    // BUG FIX: Convert C++ types to C types
    returnType = convertToCType(returnType);

    // Create C function declaration using CNodeBuilder
    FunctionDecl* CFunc = Builder.funcDecl(
        mangledName,
        returnType,
        params,
        nullptr  // No body for now - body translation handled elsewhere
    );

    return CFunc;
}

// ============================================================================
// Private Helper: Type Conversion (Phase 32.2 - Bug Fix)
// ============================================================================

QualType TemplateMonomorphizer::convertToCType(QualType Type) {
    // Handle RecordType (struct/class)
    if (const RecordType* RT = Type->getAs<RecordType>()) {
        RecordDecl* RD = RT->getDecl();

        // If it's a CXXRecordDecl (C++ class/struct), create a C struct type
        if (isa<CXXRecordDecl>(RD)) {
            // Create a new RecordDecl with TagTypeKind::Struct for C output
            std::string name = RD->getNameAsString();
            IdentifierInfo& II = Context.Idents.get(name);

            RecordDecl* CRecord = RecordDecl::Create(
                Context,
#if LLVM_VERSION_MAJOR >= 16
                TagTypeKind::Struct,
#else
                TagTypeKind::Struct,
#endif
                Context.getTranslationUnitDecl(),
                SourceLocation(),
                SourceLocation(),
                &II
            );

            // Return the new C struct type
            return Context.getRecordType(CRecord);
        }
    }

    // Handle PointerType (e.g., Wrapper<int>*)
    if (const PointerType* PT = Type->getAs<PointerType>()) {
        QualType PointeeType = convertToCType(PT->getPointeeType());
        return Context.getPointerType(PointeeType);
    }

    // Handle ReferenceType (e.g., Wrapper<int>&)
    if (const ReferenceType* RefT = Type->getAs<ReferenceType>()) {
        QualType PointeeType = convertToCType(RefT->getPointeeType());
        if (const LValueReferenceType* LRef = dyn_cast<LValueReferenceType>(RefT)) {
            return Context.getLValueReferenceType(PointeeType);
        } else if (const RValueReferenceType* RRef = dyn_cast<RValueReferenceType>(RefT)) {
            return Context.getRValueReferenceType(PointeeType);
        }
    }

    // Handle ArrayType
    if (const ArrayType* AT = Type->getAsArrayTypeUnsafe()) {
        QualType ElementType = convertToCType(AT->getElementType());
        if (const ConstantArrayType* CAT = dyn_cast<ConstantArrayType>(AT)) {
            return Context.getConstantArrayType(
                ElementType,
                CAT->getSize(),
                CAT->getSizeExpr(),
                CAT->getSizeModifier(),
                CAT->getIndexTypeCVRQualifiers()
            );
        }
    }

    // For other types, return as-is
    return Type;
}

// ============================================================================
// Private Helper: AST Creation Methods (Phase 32.1)
// ============================================================================

RecordDecl* TemplateMonomorphizer::createStruct(ClassTemplateSpecializationDecl* D,
                                                const std::string& MangledName) {
    if (!D) return nullptr;

    // Build field list (following CppToCVisitor::VisitCXXRecordDecl pattern)
    std::vector<FieldDecl*> fields;

    // BUG FIX (Bug #17): For template specializations, fields might not be populated.
    // Similar to methods, we need to get them from the template pattern.
    ClassTemplateDecl* Template = D->getSpecializedTemplate();
    CXXRecordDecl* Pattern = Template ? Template->getTemplatedDecl() : nullptr;

    // Try pattern first, fall back to specialization
    CXXRecordDecl* SourceDecl = Pattern ? Pattern : D;

    // Get template arguments for type substitution
    const TemplateArgumentList& TemplateArgs = D->getTemplateArgs();

    // BUG FIX (Bug #18): Clear nested class mappings for this instantiation
    nestedClassMappings.clear();

    // BUG FIX (Bug #17 extension): Handle nested classes inside template
    // Example: struct Node inside template<typename T> class LinkedList
    // Need to generate monomorphized versions of nested classes first

    // BUG FIX (Bug #34): First pass - populate nestedClassMappings before processing fields
    // This ensures that when we process nested struct fields (like Node::next),
    // the mapping is already available for substituteType() to use
    for (auto* Decl : SourceDecl->decls()) {
        if (CXXRecordDecl* NestedClass = dyn_cast<CXXRecordDecl>(Decl)) {
            // Skip forward declarations
            if (!NestedClass->isCompleteDefinition()) continue;

            // Skip compiler-generated
            if (NestedClass->isImplicit()) continue;

            // Generate mangled name for nested struct: OuterClass_NestedClass
            std::string nestedMangledName = MangledName + "_" + NestedClass->getNameAsString();

            // Store mapping for nested class name substitution
            // E.g., "Node" -> "LinkedList_int_Node"
            nestedClassMappings[NestedClass->getNameAsString()] = nestedMangledName;

            llvm::outs() << "  Registered nested class mapping: " << NestedClass->getNameAsString()
                         << " -> " << nestedMangledName << "\n";
        }
    }

    // Second pass - now process the nested classes with mappings in place
    std::vector<RecordDecl*> nestedStructs;
    for (auto* Decl : SourceDecl->decls()) {
        if (CXXRecordDecl* NestedClass = dyn_cast<CXXRecordDecl>(Decl)) {
            // Skip forward declarations
            if (!NestedClass->isCompleteDefinition()) continue;

            // Skip compiler-generated
            if (NestedClass->isImplicit()) continue;

            llvm::outs() << "  Processing nested class: " << NestedClass->getNameAsString() << "\n";

            // Get the mangled name from our mapping
            std::string nestedMangledName = nestedClassMappings[NestedClass->getNameAsString()];

            // Build fields for nested struct
            std::vector<FieldDecl*> nestedFields;
            for (auto* NestedField : NestedClass->fields()) {
                QualType nestedFieldType = NestedField->getType();
                std::string nestedFieldName = NestedField->getNameAsString();

                // Substitute template parameters in nested field types
                // BUG FIX (Bug #34): Now nestedClassMappings is populated, so substituteType()
                // will correctly replace Node* with LinkedList_int_Node*
                nestedFieldType = substituteType(nestedFieldType, TemplateArgs);
                nestedFieldType = convertToCType(nestedFieldType);

                FieldDecl* CNestedField = Builder.fieldDecl(nestedFieldType, nestedFieldName);
                nestedFields.push_back(CNestedField);
            }

            // Create nested struct
            RecordDecl* CNestedStruct = Builder.structDecl(nestedMangledName, nestedFields);
            nestedStructs.push_back(CNestedStruct);

            llvm::outs() << "    -> Generated struct " << nestedMangledName << " with "
                         << nestedFields.size() << " fields\n";

            // Generate constructors for nested class
            for (auto* Ctor : NestedClass->ctors()) {
                // Skip implicit constructors
                if (Ctor->isImplicit()) continue;

                // Skip copy/move constructors (handled separately)
                if (Ctor->isCopyConstructor() || Ctor->isMoveConstructor()) continue;

                llvm::outs() << "    -> Processing nested constructor: " << Ctor->getNameAsString() << "\n";

                // Build mangled constructor name: OuterClass_NestedClass__ctor
                std::string ctorName = nestedMangledName + "__ctor";

                // Build parameter list with 'this' pointer
                llvm::SmallVector<ParmVarDecl*, 8> ctorParams;

                // First parameter: 'this' pointer
                QualType thisType = Context.getPointerType(Context.getRecordType(CNestedStruct));
                ParmVarDecl* thisParam = Builder.param(thisType, "this");
                ctorParams.push_back(thisParam);

                // Add constructor parameters
                for (unsigned i = 0; i < Ctor->getNumParams(); ++i) {
                    ParmVarDecl* OrigParam = Ctor->getParamDecl(i);
                    QualType paramType = OrigParam->getType();
                    std::string paramName = OrigParam->getNameAsString();

                    // Substitute template parameters in parameter types
                    paramType = substituteType(paramType, TemplateArgs);
                    paramType = convertToCType(paramType);

                    ParmVarDecl* CParam = Builder.param(paramType, paramName);
                    ctorParams.push_back(CParam);
                }

                // Return type is void for constructors in C
                QualType returnType = Context.VoidTy;

                // Create C function declaration
                FunctionDecl* CCtorFunc = Builder.funcDecl(ctorName, returnType, ctorParams, nullptr);

                llvm::outs() << "      -> Generated constructor function: " << ctorName << "\n";
            }
        }
    }

    // Generate fields from template class
    for (auto* Field : SourceDecl->fields()) {
        // Get field type from pattern (may have template parameters like T)
        QualType fieldType = Field->getType();
        std::string fieldName = Field->getNameAsString();

        // BUG FIX (Bug #17): Substitute template parameters with concrete types
        // If we're using the pattern, T needs to be replaced with int/float/etc
        if (Pattern) {
            fieldType = substituteType(fieldType, TemplateArgs);
        }

        // Convert C++ class template types to C struct types
        fieldType = convertToCType(fieldType);

        // Create C field using CNodeBuilder
        FieldDecl* CField = Builder.fieldDecl(fieldType, fieldName);
        fields.push_back(CField);
    }

    // Create C struct using CNodeBuilder
    // Note: CNodeBuilder.structDecl automatically:
    // 1. Calls startDefinition()
    // 2. Adds fields with proper parent context
    // 3. Calls completeDefinition()
    // 4. Adds to TranslationUnitDecl
    RecordDecl* CStruct = Builder.structDecl(MangledName, fields);

    return CStruct;
}

FunctionDecl* TemplateMonomorphizer::createMethodFunction(
    CXXMethodDecl* Method,
    const std::string& ClassName,
    const TemplateArgumentList& TemplateArgs) {

    if (!Method) return nullptr;

    // Build mangled method name: ClassName_methodName
    std::string methodName = ClassName + "_" + Method->getNameAsString();

    // Build parameter list with 'this' pointer
    llvm::SmallVector<ParmVarDecl*, 8> params;

    // First parameter: 'this' pointer (ClassName*)
    QualType thisType = Context.getPointerType(
        Context.getRecordType(
            RecordDecl::Create(
                Context,
#if LLVM_VERSION_MAJOR >= 16
                TagTypeKind::Struct,
#else
                TagTypeKind::Struct,
#endif
                Context.getTranslationUnitDecl(),
                SourceLocation(),
                SourceLocation(),
                &Context.Idents.get(ClassName)
            )
        )
    );

    ParmVarDecl* thisParam = Builder.param(thisType, "this");
    params.push_back(thisParam);

    // Add original method parameters
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        ParmVarDecl* OrigParam = Method->getParamDecl(i);

        // Get parameter type from pattern (still has template parameters like T)
        QualType paramType = OrigParam->getType();
        std::string paramName = OrigParam->getNameAsString();

        // BUG FIX (Bug #17): Substitute template parameters with concrete types
        // Method comes from template pattern, so T needs to be replaced with int/float/etc
        paramType = substituteType(paramType, TemplateArgs);

        // Convert C++ types to C types
        paramType = convertToCType(paramType);

        // Create C parameter using CNodeBuilder
        ParmVarDecl* CParam = Builder.param(paramType, paramName);
        params.push_back(CParam);
    }

    // Get return type from pattern (still has template parameters like T)
    QualType returnType = Method->getReturnType();

    // BUG FIX (Bug #17): Substitute template parameters with concrete types
    returnType = substituteType(returnType, TemplateArgs);

    // Convert C++ types to C types
    returnType = convertToCType(returnType);

    // Create C function declaration using CNodeBuilder
    FunctionDecl* CFunc = Builder.funcDecl(
        methodName,
        returnType,
        params,
        nullptr  // No body for now - body translation handled elsewhere
    );

    return CFunc;
}

// ============================================================================
// Private Helper: Type Substitution (unchanged - future enhancement hook)
// ============================================================================

QualType TemplateMonomorphizer::substituteType(QualType Type,
                                               const TemplateArgumentList& TemplateArgs) {
    // Handle template parameter types (e.g., T in template<typename T>)
    if (const TemplateTypeParmType* TTPT = Type->getAs<TemplateTypeParmType>()) {
        // Get the index of this template parameter
        unsigned Index = TTPT->getIndex();

        // Check if we have a template argument for this index
        if (Index < TemplateArgs.size()) {
            const TemplateArgument& Arg = TemplateArgs[Index];
            if (Arg.getKind() == TemplateArgument::Type) {
                // Return the concrete type (e.g., int, float)
                return Arg.getAsType();
            }
        }
    }

    // BUG FIX (Bug #18): Handle nested class types
    // If type is a RecordType referring to a nested class (e.g., Node),
    // replace it with the monomorphized struct type (e.g., LinkedList_int_Node)
    if (const RecordType* RT = Type->getAs<RecordType>()) {
        RecordDecl* RD = RT->getDecl();
        std::string recordName = RD->getNameAsString();

        // Check if this is a nested class we've monomorphized
        auto it = nestedClassMappings.find(recordName);
        if (it != nestedClassMappings.end()) {
            // Create a new RecordDecl with the monomorphized name
            std::string mangledName = it->second;
            IdentifierInfo& II = Context.Idents.get(mangledName);

            RecordDecl* CRecord = RecordDecl::Create(
                Context,
#if LLVM_VERSION_MAJOR >= 16
                TagTypeKind::Struct,
#else
                TagTypeKind::Struct,
#endif
                Context.getTranslationUnitDecl(),
                SourceLocation(),
                SourceLocation(),
                &II
            );

            return Context.getRecordType(CRecord);
        }
    }

    // Handle pointer types recursively
    if (const PointerType* PT = Type->getAs<PointerType>()) {
        QualType PointeeType = substituteType(PT->getPointeeType(), TemplateArgs);
        return Context.getPointerType(PointeeType);
    }

    // Handle reference types recursively
    if (const ReferenceType* RefT = Type->getAs<ReferenceType>()) {
        QualType PointeeType = substituteType(RefT->getPointeeType(), TemplateArgs);
        if (isa<LValueReferenceType>(RefT)) {
            return Context.getLValueReferenceType(PointeeType);
        } else if (isa<RValueReferenceType>(RefT)) {
            return Context.getRValueReferenceType(PointeeType);
        }
    }

    // Handle array types recursively
    if (const ArrayType* AT = Type->getAsArrayTypeUnsafe()) {
        QualType ElementType = substituteType(AT->getElementType(), TemplateArgs);
        if (const ConstantArrayType* CAT = dyn_cast<ConstantArrayType>(AT)) {
            return Context.getConstantArrayType(
                ElementType,
                CAT->getSize(),
                CAT->getSizeExpr(),
                CAT->getSizeModifier(),
                CAT->getIndexTypeCVRQualifiers()
            );
        }
    }

    // Handle const/volatile qualifiers
    if (Type.hasLocalQualifiers()) {
        Qualifiers Quals = Type.getLocalQualifiers();
        QualType UnqualType = Type.getUnqualifiedType();
        QualType SubstitutedType = substituteType(UnqualType, TemplateArgs);
        return Context.getQualifiedType(SubstitutedType, Quals);
    }

    // For other types, return as-is
    return Type;
}

// ============================================================================
// Private Helper: Name Mangling (unchanged - keep existing logic)
// ============================================================================

std::string TemplateMonomorphizer::typeToIdentifierString(QualType Type) {
    // Convert type to valid C identifier component (no *, <, >, ::, etc.)

    // Handle references as pointers in C
    if (Type->isReferenceType()) {
        QualType pointeeType = Type->getPointeeType();
        return typeToIdentifierString(pointeeType) + "_ref";
    }

    // Handle pointer types recursively
    if (Type->isPointerType()) {
        QualType pointeeType = Type->getPointeeType();
        return typeToIdentifierString(pointeeType) + "_ptr";
    }

    // Get canonical type
    QualType canonicalType = Type.getCanonicalType();

    // Handle builtin types
    if (const BuiltinType* BT = canonicalType->getAs<BuiltinType>()) {
        switch (BT->getKind()) {
            case BuiltinType::Void: return "void";
            case BuiltinType::Bool: return "bool";
            case BuiltinType::Char_S:
            case BuiltinType::Char_U: return "char";
            case BuiltinType::SChar: return "schar";
            case BuiltinType::UChar: return "uchar";
            case BuiltinType::Short: return "short";
            case BuiltinType::UShort: return "ushort";
            case BuiltinType::Int: return "int";
            case BuiltinType::UInt: return "uint";
            case BuiltinType::Long: return "long";
            case BuiltinType::ULong: return "ulong";
            case BuiltinType::LongLong: return "llong";
            case BuiltinType::ULongLong: return "ullong";
            case BuiltinType::Float: return "float";
            case BuiltinType::Double: return "double";
            case BuiltinType::LongDouble: return "ldouble";
            default: break;
        }
    }

    // For record types (struct/class), use the simple name
    if (const RecordType* RT = canonicalType->getAs<RecordType>()) {
        RecordDecl* RD = RT->getDecl();
        return RD->getNameAsString();
    }

    // Fallback: get type string and sanitize it
    std::string typeStr = canonicalType.getAsString();

    // Remove "class " and "struct " prefixes
    size_t classPos = typeStr.find("class ");
    if (classPos != std::string::npos) {
        typeStr.erase(classPos, 6);
    }
    size_t structPos = typeStr.find("struct ");
    if (structPos != std::string::npos) {
        typeStr.erase(structPos, 7);
    }

    // Replace invalid identifier characters with underscores
    for (char& c : typeStr) {
        if (!std::isalnum(c) && c != '_') {
            c = '_';
        }
    }

    return typeStr;
}

std::string TemplateMonomorphizer::generateMangledName(const std::string& BaseName,
                                                      const TemplateArgumentList& TemplateArgs) {
    std::ostringstream name;
    name << BaseName;

    // Append template arguments
    for (unsigned i = 0; i < TemplateArgs.size(); ++i) {
        const TemplateArgument& arg = TemplateArgs[i];
        name << "_";

        switch (arg.getKind()) {
            case TemplateArgument::Type: {
                QualType argType = arg.getAsType();
                // Use typeToIdentifierString instead of typeToString for valid C identifiers
                name << typeToIdentifierString(argType);
                break;
            }
            case TemplateArgument::Integral: {
                llvm::SmallString<16> IntStr;
                arg.getAsIntegral().toString(IntStr, 10);
                name << IntStr.str().str();
                break;
            }
            case TemplateArgument::Expression:
                name << "expr";
                break;
            default:
                name << "arg";
                break;
        }
    }

    return name.str();
}

// ============================================================================
// DEPRECATED: Old String Generation Methods (Phase 32.0 - kept for reference)
// ============================================================================
// These methods are deprecated in favor of AST generation above.
// Kept temporarily for backwards compatibility and reference.
// TODO: Remove after full migration to AST-based approach is verified.
// ============================================================================

// DEPRECATED: Use monomorphizeClass() + monomorphizeClassMethods() instead
#if 0
std::string TemplateMonomorphizer::monomorphizeClass_OLD(ClassTemplateSpecializationDecl* D) {
    if (!D) return "";

    // Generate mangled name for this instantiation
    std::string mangledName = generateMangledName(
        D->getSpecializedTemplate()->getNameAsString(),
        D->getTemplateArgs()
    );

    // Generate struct definition
    std::string result = generateStruct(D, mangledName);

    // Generate method declarations
    for (auto* Decl : D->decls()) {
        if (auto* Method = dyn_cast<CXXMethodDecl>(Decl)) {
            // Skip compiler-generated methods
            if (Method->isImplicit()) continue;

            result += generateMethod(Method, mangledName, D->getTemplateArgs());
        }
    }

    return result;
}

std::string TemplateMonomorphizer::generateStruct(ClassTemplateSpecializationDecl* D,
                                                 const std::string& MangledName) {
    std::ostringstream code;

    code << "typedef struct " << MangledName << " {\n";

    // Generate fields
    for (auto* Field : D->fields()) {
        code << "    ";

        // Field type (already substituted by Clang)
        QualType fieldType = Field->getType();

        // Handle arrays - get element type first
        if (fieldType->isConstantArrayType()) {
            const ConstantArrayType* arrayType = Context.getAsConstantArrayType(fieldType);
            if (arrayType) {
                // Get element type (e.g., int from int[10])
                QualType elementType = arrayType->getElementType();
                code << typeToString(elementType);
                code << " " << Field->getNameAsString();
                code << "[" << arrayType->getSize().getZExtValue() << "]";
            }
        } else {
            // Non-array types
            code << typeToString(fieldType);
            code << " " << Field->getNameAsString();
        }

        code << ";\n";
    }

    code << "} " << MangledName << ";\n\n";

    return code.str();
}

std::string TemplateMonomorphizer::generateMethod(CXXMethodDecl* Method,
                                                 const std::string& ClassName,
                                                 const TemplateArgumentList& TemplateArgs) {
    std::ostringstream code;

    // Return type (already substituted by Clang)
    QualType returnType = Method->getReturnType();
    code << typeToString(returnType) << " ";

    // Method name: ClassName_methodName
    code << ClassName << "_" << Method->getNameAsString();

    // Parameters (with 'this' pointer)
    code << "(" << ClassName << "* this";

    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        code << ", ";
        ParmVarDecl* param = Method->getParamDecl(i);

        // Parameter type (already substituted by Clang)
        QualType paramType = param->getType();
        code << typeToString(paramType);

        code << " " << param->getNameAsString();
    }

    code << ");\n";

    return code.str();
}

std::string TemplateMonomorphizer::typeToString(QualType Type) {
    // Handle references as pointers in C
    if (Type->isReferenceType()) {
        QualType pointeeType = Type->getPointeeType();
        return typeToString(pointeeType) + "*";
    }

    // Get canonical type string
    std::string typeStr = Type.getAsString();

    // Clean up type string for C
    // Remove "class " prefix
    size_t classPos = typeStr.find("class ");
    if (classPos != std::string::npos) {
        typeStr.erase(classPos, 6);
    }

    // Remove "struct " prefix
    size_t structPos = typeStr.find("struct ");
    if (structPos != std::string::npos) {
        typeStr.erase(structPos, 7);
    }

    // Normalize pointer spacing: "int *" -> "int*", "int **" -> "int**"
    size_t pos = 0;
    while ((pos = typeStr.find(" *", pos)) != std::string::npos) {
        typeStr.erase(pos, 1);  // Remove the space before *
    }

    return typeStr;
}
#endif
