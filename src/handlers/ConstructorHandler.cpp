/**
 * @file ConstructorHandler.cpp
 * @brief Implementation of ConstructorHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 *
 * Translation Strategy:
 * 1. Detect CXXConstructorDecl
 * 2. Extract class name
 * 3. Generate mangled function name (ClassName_init or ClassName_init_types)
 * 4. Create 'this' parameter: struct ClassName* this
 * 5. Add constructor parameters after 'this'
 * 6. Handle member initializer list (convert to assignments)
 * 7. Translate constructor body
 * 8. Return C FunctionDecl with void return type
 */

#include "handlers/ConstructorHandler.h"
#include "handlers/HandlerContext.h"
#include "MultipleInheritanceAnalyzer.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/RecordLayout.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool ConstructorHandler::canHandle(const clang::Decl* D) const {
    // Check if this is a CXXConstructorDecl
    return llvm::isa<clang::CXXConstructorDecl>(D);
}

clang::Decl* ConstructorHandler::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    const auto* ctor = llvm::cast<clang::CXXConstructorDecl>(D);

    // Get parent class (the class this constructor belongs to)
    const auto* parentClass = ctor->getParent();
    if (!parentClass) {
        return nullptr; // Should never happen
    }

    std::string className = parentClass->getNameAsString();

    // Generate mangled function name
    std::string funcName = generateConstructorName(className, ctor);

    // Create 'this' parameter
    // IMPORTANT: Must use C RecordDecl, not C++ RecordDecl
    // Look up the C RecordDecl by name (similar to MethodHandler approach)
    clang::ASTContext& cCtx = ctx.getCContext();
    clang::RecordDecl* cRecordDecl = nullptr;

    // Try to find the C RecordDecl in the translation unit
    auto* TU = cCtx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
            if (RD->getName() == className) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        // RecordHandler should have created the struct already
        // This shouldn't happen if RecordHandler was called first
        return nullptr;
    }

    clang::QualType classType = cCtx.getRecordType(cRecordDecl);
    clang::ParmVarDecl* thisParam = createThisParameter(classType, ctx);

    // Translate constructor parameters
    std::vector<clang::ParmVarDecl*> ctorParams = translateParameters(ctor, ctx);

    // Combine 'this' parameter with constructor parameters
    std::vector<clang::ParmVarDecl*> allParams;
    allParams.push_back(thisParam);
    allParams.insert(allParams.end(), ctorParams.begin(), ctorParams.end());

    // Get void return type
    clang::ASTContext& cContext = ctx.getCContext();
    clang::QualType returnType = cContext.VoidTy;

    // Create C function using CNodeBuilder
    clang::CNodeBuilder& builder = ctx.getBuilder();
    clang::FunctionDecl* cFunc = builder.funcDecl(
        funcName,
        returnType,
        allParams,
        nullptr      // No body yet (body translation handled separately)
    );

    // Register mapping
    ctx.registerDecl(ctor, cFunc);

    // Step 7: Prepare lpVtbl initialization (Phase 45 Group 3, Phase 46 Group 3)
    std::vector<clang::Stmt*> lpVtblInitStmts;
    if (parentClass->isPolymorphic()) {
        lpVtblInitStmts = injectLpVtblInit(parentClass, thisParam, ctx);
    }

    // Step 8: Build constructor body
    // Order (Phase 46 Group 3):
    // Task 7: lpVtbl initialization MUST be FIRST (before any other initialization)
    // Task 8: Then base constructor calls (they initialize base vtables)
    // Then: Member initializers
    std::vector<clang::Stmt*> bodyStmts;

    // Step 8a: Add lpVtbl initialization(s) FIRST (Task 7)
    bodyStmts.insert(bodyStmts.end(), lpVtblInitStmts.begin(), lpVtblInitStmts.end());

    // Step 8b: Add base constructor calls AFTER lpVtbl init (Task 8)
    auto baseCtorCalls = generateBaseConstructorCalls(ctor, thisParam, ctx);
    bodyStmts.insert(bodyStmts.end(), baseCtorCalls.begin(), baseCtorCalls.end());

    // TODO: Add member initializer list translations here
    // For now, we have base calls and lpVtbl init

    // Create CompoundStmt (constructor body)
    clang::CompoundStmt* body = clang::CompoundStmt::Create(
        cContext,
        bodyStmts,
        clang::FPOptionsOverride(),
        clang::SourceLocation(),
        clang::SourceLocation()
    );

    // Set the function body
    cFunc->setBody(body);

    return cFunc;
}

std::string ConstructorHandler::generateConstructorName(
    const std::string& className,
    const clang::CXXConstructorDecl* ctor
) {
    // Base name: ClassName_init
    std::string baseName = className + "_init";

    // If no parameters, just return base name
    if (ctor->getNumParams() == 0) {
        return baseName;
    }

    // Add parameter types to name for overload resolution
    // Format: ClassName_init_type1_type2_...
    std::string mangledName = baseName;

    for (const auto* param : ctor->parameters()) {
        clang::QualType paramType = param->getType();
        std::string typeName = getSimpleTypeName(paramType);
        mangledName += "_" + typeName;
    }

    return mangledName;
}

std::vector<clang::ParmVarDecl*> ConstructorHandler::translateParameters(
    const clang::CXXConstructorDecl* ctor,
    HandlerContext& ctx
) {
    std::vector<clang::ParmVarDecl*> cParams;
    clang::ASTContext& cContext = ctx.getCContext();

    // Translate each parameter
    for (const auto* cppParam : ctor->parameters()) {
        // Create identifier for parameter name
        clang::IdentifierInfo& II = cContext.Idents.get(cppParam->getNameAsString());

        // Translate parameter type (convert references to pointers)
        clang::QualType cppParamType = cppParam->getType();
        clang::QualType cParamType = translateType(cppParamType, ctx);

        // Create C parameter with translated type
        clang::ParmVarDecl* cParam = clang::ParmVarDecl::Create(
            cContext,
            cContext.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            cParamType,
            cContext.getTrivialTypeSourceInfo(cParamType),
            clang::SC_None,
            nullptr  // No default argument
        );

        cParams.push_back(cParam);

        // Register parameter mapping for later reference
        ctx.registerDecl(cppParam, cParam);
    }

    return cParams;
}

clang::ParmVarDecl* ConstructorHandler::createThisParameter(
    clang::QualType recordType,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();

    // Create identifier for 'this'
    clang::IdentifierInfo& II = cContext.Idents.get("this");

    // Create pointer type: struct ClassName* this
    clang::QualType thisType = cContext.getPointerType(recordType);

    // Create parameter declaration
    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cContext,
        cContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        thisType,
        cContext.getTrivialTypeSourceInfo(thisType),
        clang::SC_None,
        nullptr  // No default argument
    );

    return thisParam;
}

clang::QualType ConstructorHandler::translateType(
    clang::QualType cppType,
    HandlerContext& ctx
) {
    clang::ASTContext& cCtx = ctx.getCContext();

    // Check for lvalue reference (T&)
    if (const auto* lvalRefType = llvm::dyn_cast<clang::LValueReferenceType>(cppType.getTypePtr())) {
        // Transform T& → T*
        clang::QualType pointeeType = lvalRefType->getPointeeType();
        return cCtx.getPointerType(pointeeType);
    }

    // Check for rvalue reference (T&&)
    if (const auto* rvalRefType = llvm::dyn_cast<clang::RValueReferenceType>(cppType.getTypePtr())) {
        // Transform T&& → T*
        clang::QualType pointeeType = rvalRefType->getPointeeType();
        return cCtx.getPointerType(pointeeType);
    }

    // For non-reference types, pass through unchanged
    return cppType;
}

std::string ConstructorHandler::getSimpleTypeName(clang::QualType type) const {
    // Remove qualifiers (const, volatile)
    type = type.getUnqualifiedType();

    // Check for pointer types
    if (type->isPointerType()) {
        clang::QualType pointeeType = type->getPointeeType();
        std::string pointeeName = getSimpleTypeName(pointeeType);
        return pointeeName + "ptr";
    }

    // Check for reference types (should be converted to pointers by translateType)
    if (type->isReferenceType()) {
        clang::QualType pointeeType = type.getNonReferenceType();
        std::string pointeeName = getSimpleTypeName(pointeeType);
        return pointeeName + "ptr";
    }

    // Check for built-in types
    if (type->isBuiltinType()) {
        const auto* builtinType = llvm::cast<clang::BuiltinType>(type.getTypePtr());
        switch (builtinType->getKind()) {
            case clang::BuiltinType::Void:
                return "void";
            case clang::BuiltinType::Bool:
                return "bool";
            case clang::BuiltinType::Char_S:
            case clang::BuiltinType::Char_U:
            case clang::BuiltinType::Char8:
            case clang::BuiltinType::Char16:
            case clang::BuiltinType::Char32:
                return "char";
            case clang::BuiltinType::Short:
            case clang::BuiltinType::UShort:
                return "short";
            case clang::BuiltinType::Int:
            case clang::BuiltinType::UInt:
                return "int";
            case clang::BuiltinType::Long:
            case clang::BuiltinType::ULong:
                return "long";
            case clang::BuiltinType::LongLong:
            case clang::BuiltinType::ULongLong:
                return "longlong";
            case clang::BuiltinType::Float:
                return "float";
            case clang::BuiltinType::Double:
                return "double";
            case clang::BuiltinType::LongDouble:
                return "longdouble";
            default:
                return "unknown";
        }
    }

    // Check for record types (struct/class)
    if (type->isRecordType()) {
        const auto* recordType = llvm::cast<clang::RecordType>(type.getTypePtr());
        const auto* recordDecl = recordType->getDecl();
        return recordDecl->getNameAsString();
    }

    // Check for enum types
    if (type->isEnumeralType()) {
        const auto* enumType = llvm::cast<clang::EnumType>(type.getTypePtr());
        const auto* enumDecl = enumType->getDecl();
        return enumDecl->getNameAsString();
    }

    // Default: use type as string
    return type.getAsString();
}

std::vector<clang::Stmt*> ConstructorHandler::injectLpVtblInit(
    const clang::CXXRecordDecl* parentClass,
    clang::ParmVarDecl* thisParam,
    HandlerContext& ctx
) {
    std::vector<clang::Stmt*> stmts;

    // Only inject for polymorphic classes
    if (!parentClass || !parentClass->isPolymorphic()) {
        return stmts;
    }

    clang::ASTContext& cCtx = ctx.getCContext();
    clang::ASTContext& cppCtx = ctx.getCppContext();
    std::string className = parentClass->getNameAsString();

    // Phase 46 Group 3 Task 7: Use MultipleInheritanceAnalyzer to identify all polymorphic bases
    // For derived classes with polymorphic bases
    MultipleInheritanceAnalyzer miAnalyzer(cppCtx);
    auto bases = miAnalyzer.analyzePolymorphicBases(parentClass);

    // Special case: If this class has NO polymorphic bases (i.e., it's a base class itself),
    // we still need to initialize its own lpVtbl
    bool isBaseClassWithNoBases = bases.empty() && parentClass->getNumBases() == 0;

    // Find the C struct that RecordHandler created
    clang::RecordDecl* cRecordDecl = nullptr;
    auto* TU = cCtx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
            if (RD->getName() == className) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        return stmts;  // C struct not found (shouldn't happen)
    }

    // Generate initialization statement for each polymorphic base
    // Order: lpVtbl, lpVtbl2, lpVtbl3, ...
    for (const auto& baseInfo : bases) {
        std::string baseName = baseInfo.BaseDecl->getNameAsString();
        std::string lpVtblFieldName = baseInfo.VtblFieldName;  // "lpVtbl", "lpVtbl2", "lpVtbl3", ...

        // Find the lpVtbl field in C struct
        clang::FieldDecl* lpVtblField = nullptr;
        for (auto* field : cRecordDecl->fields()) {
            if (field->getNameAsString() == lpVtblFieldName) {
                lpVtblField = field;
                break;
            }
        }

        if (!lpVtblField) {
            continue;  // Field not found (shouldn't happen if RecordHandler worked correctly)
        }

        // Create LHS: this->lpVtbl (or this->lpVtbl2, this->lpVtbl3, ...)
        clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
            cCtx,
            clang::NestedNameSpecifierLoc(),
            clang::SourceLocation(),
            thisParam,
            false,
            clang::SourceLocation(),
            thisParam->getType(),
            clang::VK_LValue
        );

        clang::MemberExpr* lpVtblMemberExpr = clang::MemberExpr::Create(
            cCtx,
            thisExpr,
            true,  // isArrow
            clang::SourceLocation(),
            clang::NestedNameSpecifierLoc(),
            clang::SourceLocation(),
            lpVtblField,
            clang::DeclAccessPair::make(lpVtblField, clang::AS_public),
            clang::DeclarationNameInfo(lpVtblField->getDeclName(), clang::SourceLocation()),
            nullptr,
            lpVtblField->getType(),
            clang::VK_LValue,
            clang::OK_Ordinary,
            clang::NOUR_None
        );

        // Create RHS: &ClassName_BaseName_vtable_instance
        std::string vtableInstanceName = className + "_" + baseName + "_vtable_instance";

        // Find or create vtable instance variable
        clang::VarDecl* vtableInstanceVar = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* VD = llvm::dyn_cast<clang::VarDecl>(D)) {
                if (VD->getNameAsString() == vtableInstanceName) {
                    vtableInstanceVar = VD;
                    break;
                }
            }
        }

        if (!vtableInstanceVar) {
            // Create forward declaration for vtable instance
            std::string vtableStructName = className + "_" + baseName + "_vtable";
            clang::RecordDecl* vtableStruct = nullptr;

            for (auto* D : TU->decls()) {
                if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                    if (RD->getNameAsString() == vtableStructName) {
                        vtableStruct = RD;
                        break;
                    }
                }
            }

            if (!vtableStruct) {
                clang::IdentifierInfo& vtableII = cCtx.Idents.get(vtableStructName);
                vtableStruct = clang::RecordDecl::Create(
                    cCtx,
                    clang::TagTypeKind::Struct,
                    TU,
                    clang::SourceLocation(),
                    clang::SourceLocation(),
                    &vtableII
                );
                vtableStruct->startDefinition();
                vtableStruct->completeDefinition();
            }

            clang::QualType vtableType = cCtx.getRecordType(vtableStruct);
            clang::QualType constVtableType = cCtx.getConstType(vtableType);

            clang::IdentifierInfo& instanceII = cCtx.Idents.get(vtableInstanceName);
            vtableInstanceVar = clang::VarDecl::Create(
                cCtx,
                TU,
                clang::SourceLocation(),
                clang::SourceLocation(),
                &instanceII,
                constVtableType,
                cCtx.getTrivialTypeSourceInfo(constVtableType),
                clang::SC_Extern
            );

            TU->addDecl(vtableInstanceVar);
        }

        // Create &vtable_instance
        clang::DeclRefExpr* vtableInstanceExpr = clang::DeclRefExpr::Create(
            cCtx,
            clang::NestedNameSpecifierLoc(),
            clang::SourceLocation(),
            vtableInstanceVar,
            false,
            clang::SourceLocation(),
            vtableInstanceVar->getType(),
            clang::VK_LValue
        );

        clang::QualType ptrType = cCtx.getPointerType(vtableInstanceVar->getType());
        clang::UnaryOperator* addrOfExpr = clang::UnaryOperator::Create(
            cCtx,
            vtableInstanceExpr,
            clang::UO_AddrOf,
            ptrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            clang::SourceLocation(),
            false,
            clang::FPOptionsOverride()
        );

        // Create assignment: this->lpVtbl = &ClassName_BaseName_vtable_instance
        clang::BinaryOperator* assignExpr = clang::BinaryOperator::Create(
            cCtx,
            lpVtblMemberExpr,
            addrOfExpr,
            clang::BO_Assign,
            lpVtblField->getType(),
            clang::VK_LValue,
            clang::OK_Ordinary,
            clang::SourceLocation(),
            clang::FPOptionsOverride()
        );

        stmts.push_back(assignExpr);
    }

    // Handle base class with no bases (single inheritance root)
    if (isBaseClassWithNoBases) {
        // Find lpVtbl field
        clang::FieldDecl* lpVtblField = nullptr;
        for (auto* field : cRecordDecl->fields()) {
            if (field->getNameAsString() == "lpVtbl") {
                lpVtblField = field;
                break;
            }
        }

        if (lpVtblField) {
            // Create this->lpVtbl = &ClassName_vtable_instance
            clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
                cCtx,
                clang::NestedNameSpecifierLoc(),
                clang::SourceLocation(),
                thisParam,
                false,
                clang::SourceLocation(),
                thisParam->getType(),
                clang::VK_LValue
            );

            clang::MemberExpr* lpVtblMemberExpr = clang::MemberExpr::Create(
                cCtx,
                thisExpr,
                true,
                clang::SourceLocation(),
                clang::NestedNameSpecifierLoc(),
                clang::SourceLocation(),
                lpVtblField,
                clang::DeclAccessPair::make(lpVtblField, clang::AS_public),
                clang::DeclarationNameInfo(lpVtblField->getDeclName(), clang::SourceLocation()),
                nullptr,
                lpVtblField->getType(),
                clang::VK_LValue,
                clang::OK_Ordinary,
                clang::NOUR_None
            );

            // For base class: ClassName_vtable_instance (not ClassName_ClassName_vtable_instance)
            std::string vtableInstanceName = className + "_vtable_instance";

            // Find or create vtable instance
            clang::VarDecl* vtableInstanceVar = nullptr;
            for (auto* D : TU->decls()) {
                if (auto* VD = llvm::dyn_cast<clang::VarDecl>(D)) {
                    if (VD->getNameAsString() == vtableInstanceName) {
                        vtableInstanceVar = VD;
                        break;
                    }
                }
            }

            if (!vtableInstanceVar) {
                std::string vtableStructName = className + "_vtable";
                clang::RecordDecl* vtableStruct = nullptr;

                for (auto* D : TU->decls()) {
                    if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                        if (RD->getNameAsString() == vtableStructName) {
                            vtableStruct = RD;
                            break;
                        }
                    }
                }

                if (!vtableStruct) {
                    clang::IdentifierInfo& vtableII = cCtx.Idents.get(vtableStructName);
                    vtableStruct = clang::RecordDecl::Create(
                        cCtx,
                        clang::TagTypeKind::Struct,
                        TU,
                        clang::SourceLocation(),
                        clang::SourceLocation(),
                        &vtableII
                    );
                    vtableStruct->startDefinition();
                    vtableStruct->completeDefinition();
                }

                clang::QualType vtableType = cCtx.getRecordType(vtableStruct);
                clang::QualType constVtableType = cCtx.getConstType(vtableType);

                clang::IdentifierInfo& instanceII = cCtx.Idents.get(vtableInstanceName);
                vtableInstanceVar = clang::VarDecl::Create(
                    cCtx,
                    TU,
                    clang::SourceLocation(),
                    clang::SourceLocation(),
                    &instanceII,
                    constVtableType,
                    cCtx.getTrivialTypeSourceInfo(constVtableType),
                    clang::SC_Extern
                );

                TU->addDecl(vtableInstanceVar);
            }

            clang::DeclRefExpr* vtableInstanceExpr = clang::DeclRefExpr::Create(
                cCtx,
                clang::NestedNameSpecifierLoc(),
                clang::SourceLocation(),
                vtableInstanceVar,
                false,
                clang::SourceLocation(),
                vtableInstanceVar->getType(),
                clang::VK_LValue
            );

            clang::QualType ptrType = cCtx.getPointerType(vtableInstanceVar->getType());
            clang::UnaryOperator* addrOfExpr = clang::UnaryOperator::Create(
                cCtx,
                vtableInstanceExpr,
                clang::UO_AddrOf,
                ptrType,
                clang::VK_PRValue,
                clang::OK_Ordinary,
                clang::SourceLocation(),
                false,
                clang::FPOptionsOverride()
            );

            clang::BinaryOperator* assignExpr = clang::BinaryOperator::Create(
                cCtx,
                lpVtblMemberExpr,
                addrOfExpr,
                clang::BO_Assign,
                lpVtblField->getType(),
                clang::VK_LValue,
                clang::OK_Ordinary,
                clang::SourceLocation(),
                clang::FPOptionsOverride()
            );

            stmts.push_back(assignExpr);
        }
    }

    return stmts;
}

std::vector<clang::Stmt*> ConstructorHandler::generateBaseConstructorCalls(
    const clang::CXXConstructorDecl* ctor,
    clang::ParmVarDecl* thisParam,
    HandlerContext& ctx
) {
    std::vector<clang::Stmt*> calls;

    const auto* parentClass = ctor->getParent();
    if (!parentClass) {
        return calls;  // No parent class
    }

    // Iterate through base classes
    unsigned baseIndex = 0;
    for (const auto& base : parentClass->bases()) {
        const auto* baseClass = base.getType()->getAsCXXRecordDecl();
        if (!baseClass) continue;

        // Calculate offset for this base
        // Primary base (first) has offset 0
        // Non-primary bases have non-zero offsets
        unsigned offset = 0;
        if (baseIndex > 0) {
            // For non-primary bases, we need to calculate offset
            // For now, use MultipleInheritanceAnalyzer if available
            // Simple approach: non-primary bases use offsetof
            clang::ASTContext& cppCtx = ctx.getCppContext();
            if (parentClass->isCompleteDefinition()) {
                const clang::ASTRecordLayout& layout = cppCtx.getASTRecordLayout(parentClass);
                clang::CharUnits baseOffset = layout.getBaseClassOffset(baseClass);
                offset = static_cast<unsigned>(baseOffset.getQuantity());
            }
        }

        // Create base constructor call
        clang::CallExpr* call = createBaseConstructorCall(baseClass, thisParam, offset, ctx);
        if (call) {
            calls.push_back(call);
        }

        baseIndex++;
    }

    return calls;
}

clang::CallExpr* ConstructorHandler::createBaseConstructorCall(
    const clang::CXXRecordDecl* baseClass,
    clang::ParmVarDecl* thisParam,
    unsigned offset,
    HandlerContext& ctx
) {
    clang::ASTContext& cCtx = ctx.getCContext();
    std::string baseName = baseClass->getNameAsString();
    std::string baseCtorName = baseName + "_init";

    // Step 1: Find or create base constructor function declaration
    clang::FunctionDecl* baseCtorFunc = nullptr;
    auto* TU = cCtx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == baseCtorName) {
                baseCtorFunc = FD;
                break;
            }
        }
    }

    // If not found, create forward declaration
    if (!baseCtorFunc) {
        // Create base constructor function declaration
        // void BaseName_init(struct BaseName* this);

        // Find base struct
        clang::RecordDecl* baseStruct = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                if (RD->getNameAsString() == baseName) {
                    baseStruct = RD;
                    break;
                }
            }
        }

        if (!baseStruct) {
            // Create base struct if needed
            clang::IdentifierInfo& II = cCtx.Idents.get(baseName);
            baseStruct = clang::RecordDecl::Create(
                cCtx,
                clang::TagTypeKind::Struct,
                TU,
                clang::SourceLocation(),
                clang::SourceLocation(),
                &II
            );
            baseStruct->startDefinition();
            baseStruct->completeDefinition();
            TU->addDecl(baseStruct);
        }

        // Create this parameter for base constructor
        clang::QualType baseType = cCtx.getRecordType(baseStruct);
        clang::QualType basePtrType = cCtx.getPointerType(baseType);

        clang::IdentifierInfo& thisII = cCtx.Idents.get("this");
        clang::ParmVarDecl* baseThisParam = clang::ParmVarDecl::Create(
            cCtx,
            TU,
            clang::SourceLocation(),
            clang::SourceLocation(),
            &thisII,
            basePtrType,
            cCtx.getTrivialTypeSourceInfo(basePtrType),
            clang::SC_None,
            nullptr
        );

        // Create function declaration
        clang::IdentifierInfo& funcII = cCtx.Idents.get(baseCtorName);
        baseCtorFunc = clang::FunctionDecl::Create(
            cCtx,
            TU,
            clang::SourceLocation(),
            clang::SourceLocation(),
            clang::DeclarationName(&funcII),
            cCtx.VoidTy,
            cCtx.getTrivialTypeSourceInfo(cCtx.VoidTy),
            clang::SC_None
        );

        baseCtorFunc->setParams({baseThisParam});
        TU->addDecl(baseCtorFunc);
    }

    // Step 2: Create argument expression (this pointer with cast and offset)
    // For primary base (offset == 0): (struct BaseName*)this
    // For non-primary base: (struct BaseName*)((char*)this + offset)

    // Create DeclRefExpr for 'this'
    clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
        cCtx,
        clang::NestedNameSpecifierLoc(),
        clang::SourceLocation(),
        thisParam,
        false,
        clang::SourceLocation(),
        thisParam->getType(),
        clang::VK_LValue
    );

    clang::Expr* adjustedThis = thisExpr;

    // If non-primary base (offset > 0), add pointer arithmetic
    if (offset > 0) {
        // Cast this to char*
        clang::QualType charPtrType = cCtx.getPointerType(cCtx.CharTy);
        clang::CStyleCastExpr* charCast = clang::CStyleCastExpr::Create(
            cCtx,
            charPtrType,
            clang::VK_PRValue,
            clang::CK_BitCast,
            thisExpr,
            nullptr,
            clang::FPOptionsOverride(),
            cCtx.getTrivialTypeSourceInfo(charPtrType),
            clang::SourceLocation(),
            clang::SourceLocation()
        );

        // Create offset literal
        llvm::APInt offsetValue(32, offset);
        clang::IntegerLiteral* offsetLit = clang::IntegerLiteral::Create(
            cCtx,
            offsetValue,
            cCtx.IntTy,
            clang::SourceLocation()
        );

        // Add offset: (char*)this + offset
        clang::BinaryOperator* addExpr = clang::BinaryOperator::Create(
            cCtx,
            charCast,
            offsetLit,
            clang::BO_Add,
            charPtrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            clang::SourceLocation(),
            clang::FPOptionsOverride()
        );

        adjustedThis = addExpr;
    }

    // Cast to (struct BaseName*)
    // Find base struct type
    clang::RecordDecl* baseStruct = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
            if (RD->getNameAsString() == baseName) {
                baseStruct = RD;
                break;
            }
        }
    }

    if (!baseStruct) {
        return nullptr;  // Should not happen
    }

    clang::QualType baseType = cCtx.getRecordType(baseStruct);
    clang::QualType basePtrType = cCtx.getPointerType(baseType);

    clang::CStyleCastExpr* baseCast = clang::CStyleCastExpr::Create(
        cCtx,
        basePtrType,
        clang::VK_PRValue,
        clang::CK_BitCast,
        adjustedThis,
        nullptr,
        clang::FPOptionsOverride(),
        cCtx.getTrivialTypeSourceInfo(basePtrType),
        clang::SourceLocation(),
        clang::SourceLocation()
    );

    // Step 3: Create CallExpr: BaseClass_init((struct BaseClass*)this)
    std::vector<clang::Expr*> args = {baseCast};

    clang::CallExpr* callExpr = clang::CallExpr::Create(
        cCtx,
        clang::DeclRefExpr::Create(
            cCtx,
            clang::NestedNameSpecifierLoc(),
            clang::SourceLocation(),
            baseCtorFunc,
            false,
            clang::SourceLocation(),
            baseCtorFunc->getType(),
            clang::VK_LValue
        ),
        args,
        cCtx.VoidTy,
        clang::VK_PRValue,
        clang::SourceLocation(),
        clang::FPOptionsOverride()
    );

    return callExpr;
}

} // namespace cpptoc
