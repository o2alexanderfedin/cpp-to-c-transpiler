/**
 * @file RecordHandler.cpp
 * @brief Implementation of RecordHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 *
 * Implementation follows the specification in:
 * @see include/handlers/RecordHandler.h
 */

#include "handlers/RecordHandler.h"
#include "handlers/HandlerContext.h"
#include "helpers/VtableTypedefGenerator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/VTableBuilder.h"
#include "llvm/Support/Casting.h"
#include <functional>
#include <set>
#include <map>
#include <vector>

namespace cpptoc {

bool RecordHandler::canHandle(const clang::Decl* D) const {
    // Handle RecordDecl (both struct and class)
    // For Phase 43, we only handle C-style structs (no methods)
    // Methods will be handled in Phase 44
    if (const auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
        // Skip CXXRecordDecl if it has methods (Phase 44)
        // For now, accept all RecordDecl
        return true;
    }
    return false;
}

clang::Decl* RecordHandler::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    const auto* cppRecord = llvm::cast<clang::RecordDecl>(D);

    // Step 1: Extract record properties
    std::string name = cppRecord->getNameAsString();
    clang::TagTypeKind tagKind = cppRecord->getTagKind();

    // Step 2: Normalize class keyword to struct for C
    // In C, we only have struct (no class keyword)
    if (tagKind == clang::TagTypeKind::Class) {
        tagKind = clang::TagTypeKind::Struct;
    }

    // Step 3: Check if this is a forward declaration or complete definition
    bool isCompleteDefinition = cppRecord->isCompleteDefinition();

    // Step 4: Create C record declaration
    clang::ASTContext& cCtx = ctx.getCContext();

    // Create identifier for the record name
    // Anonymous structs have empty names
    clang::IdentifierInfo* II = nullptr;
    if (!name.empty()) {
        II = &cCtx.Idents.get(name);
    }

    // Create RecordDecl in C context
    // Use TranslationUnitDecl as parent for top-level structs
    // Nested structs will be handled by translateNestedRecords
    clang::DeclContext* parentContext = cCtx.getTranslationUnitDecl();

    clang::RecordDecl* cRecord = clang::RecordDecl::Create(
        cCtx,
        tagKind,
        parentContext,
        clang::SourceLocation(),
        clang::SourceLocation(),
        II
    );

    // Step 5: Register mapping early so nested structs can reference it
    ctx.registerDecl(cppRecord, cRecord);

    // Step 6: If this is a complete definition, translate fields and nested records
    if (isCompleteDefinition) {
        // Start the definition
        cRecord->startDefinition();

        // Translate nested records first (they may be referenced by fields)
        translateNestedRecords(cppRecord, cRecord, ctx);

        // Step 6a: Inject lpVtbl field for polymorphic classes (Phase 45 Task 3)
        // Must be FIRST field for COM/DCOM ABI compatibility
        if (const auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord)) {
            if (cxxRecord->isPolymorphic()) {
                injectLpVtblField(cxxRecord, cRecord, ctx);
            }
        }

        // Translate fields (after lpVtbl injection)
        translateFields(cppRecord, cRecord, ctx);

        // Complete the definition
        cRecord->completeDefinition();

        // Step 7: Generate vtable struct for polymorphic classes (Phase 45)
        if (const auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord)) {
            if (cxxRecord->isPolymorphic()) {
                generateVtableStruct(cxxRecord, ctx);

                // Step 8: Generate vtable instance for polymorphic classes (Phase 45 Task 4)
                generateVtableInstance(cxxRecord, ctx);
            }
        }
    }

    return cRecord;
}

void RecordHandler::translateFields(
    const clang::RecordDecl* cppRecord,
    clang::RecordDecl* cRecord,
    HandlerContext& ctx
) {
    clang::ASTContext& cCtx = ctx.getCContext();
    clang::ASTContext& cppCtx = ctx.getCppContext();

    // Translate each field
    // Note: Access specifiers (public/private/protected) are automatically stripped
    // because cppRecord->fields() only iterates over FieldDecl nodes,
    // skipping AccessSpecDecl nodes. C has no access control - all fields are accessible.
    for (const auto* cppField : cppRecord->fields()) {
        // Extract field properties
        std::string name = cppField->getNameAsString();
        clang::QualType cppType = cppField->getType();

        // Translate type from C++ context to C context
        // For basic types, we need to recreate them in the C context
        clang::QualType cType;

        if (cppType->isBuiltinType()) {
            // Built-in types: int, float, char, etc.
            // These are context-independent, we can use the C context's builtin types
            const clang::BuiltinType* builtinType = cppType->getAs<clang::BuiltinType>();
            switch (builtinType->getKind()) {
                case clang::BuiltinType::Int:
                    cType = cCtx.IntTy;
                    break;
                case clang::BuiltinType::Float:
                    cType = cCtx.FloatTy;
                    break;
                case clang::BuiltinType::Double:
                    cType = cCtx.DoubleTy;
                    break;
                case clang::BuiltinType::Char_S:
                case clang::BuiltinType::Char_U:
                    cType = cCtx.CharTy;
                    break;
                case clang::BuiltinType::Long:
                    cType = cCtx.LongTy;
                    break;
                case clang::BuiltinType::Short:
                    cType = cCtx.ShortTy;
                    break;
                case clang::BuiltinType::UInt:
                    cType = cCtx.UnsignedIntTy;
                    break;
                case clang::BuiltinType::Bool:
                    cType = cCtx.BoolTy;
                    break;
                default:
                    // For other builtin types, use IntTy as fallback
                    cType = cCtx.IntTy;
                    break;
            }

            // Preserve qualifiers (const, volatile)
            if (cppType.isConstQualified()) {
                cType.addConst();
            }
            if (cppType.isVolatileQualified()) {
                cType.addVolatile();
            }
        } else if (cppType->isPointerType()) {
            // Pointer types: recursively translate pointee type
            // For now, just use the type as-is (will fix later if needed)
            cType = cppType;
        } else if (cppType->isArrayType()) {
            // Array types: preserve for now
            cType = cppType;
        } else if (cppType->isRecordType()) {
            // Record types: will be translated separately
            // For now, use as-is (will fix when we handle struct type references)
            cType = cppType;
        } else {
            // Unknown type, use as-is for now
            cType = cppType;
        }

        // Create identifier
        clang::IdentifierInfo& II = cCtx.Idents.get(name);

        // Create C field declaration with cRecord as parent
        clang::FieldDecl* cField = clang::FieldDecl::Create(
            cCtx,
            cRecord, // Parent is the containing struct
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            cType,
            cCtx.getTrivialTypeSourceInfo(cType),
            nullptr, // No bitwidth
            false,   // Not mutable
            clang::ICIS_NoInit // No in-class initializer
        );

        // Add field to C record
        cRecord->addDecl(cField);

        // Register mapping
        ctx.registerDecl(cppField, cField);
    }
}

void RecordHandler::translateNestedRecords(
    const clang::RecordDecl* cppRecord,
    clang::RecordDecl* cRecord,
    HandlerContext& ctx
) {
    // Strategy: Keep nested structs in place (C supports nested struct declarations)
    // Iterate through all declarations in the C++ record
    for (const auto* decl : cppRecord->decls()) {
        // Check if this is a nested record declaration
        if (const auto* nestedCppRecord = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            // Skip implicit declarations
            if (nestedCppRecord->isImplicit()) {
                continue;
            }

            // Translate the nested record
            std::string nestedName = nestedCppRecord->getNameAsString();
            clang::TagTypeKind tagKind = nestedCppRecord->getTagKind();

            // Normalize class to struct
            if (tagKind == clang::TagTypeKind::Class) {
                tagKind = clang::TagTypeKind::Struct;
            }

            // Check if complete definition
            bool isCompleteDefinition = nestedCppRecord->isCompleteDefinition();

            // Create identifier for nested record
            clang::ASTContext& cCtx = ctx.getCContext();
            clang::IdentifierInfo* II = nullptr;
            if (!nestedName.empty()) {
                II = &cCtx.Idents.get(nestedName);
            }

            // Create nested RecordDecl with cRecord as parent
            clang::RecordDecl* nestedCRecord = clang::RecordDecl::Create(
                cCtx,
                tagKind,
                cRecord, // Parent is the containing struct
                clang::SourceLocation(),
                clang::SourceLocation(),
                II
            );

            // Register mapping
            ctx.registerDecl(nestedCppRecord, nestedCRecord);

            // If complete definition, translate its fields and nested records recursively
            if (isCompleteDefinition) {
                nestedCRecord->startDefinition();

                // Recursively translate nested records (handle multiple levels)
                translateNestedRecords(nestedCppRecord, nestedCRecord, ctx);

                // Translate fields
                translateFields(nestedCppRecord, nestedCRecord, ctx);

                nestedCRecord->completeDefinition();
            }

            // Add nested record to parent record
            cRecord->addDecl(nestedCRecord);
        }
    }
}

clang::RecordDecl* RecordHandler::generateVtableStruct(
    const clang::CXXRecordDecl* cxxRecord,
    HandlerContext& ctx
) {
    // Only generate vtable for polymorphic classes
    if (!cxxRecord || !cxxRecord->isPolymorphic()) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();
    std::string className = cxxRecord->getNameAsString();
    std::string vtableName = className + "_vtable";

    // Create vtable struct identifier
    clang::IdentifierInfo& vtableII = cCtx.Idents.get(vtableName);

    // Create vtable struct
    clang::RecordDecl* vtableStruct = clang::RecordDecl::Create(
        cCtx,
        clang::TagTypeKind::Struct,
        cCtx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &vtableII
    );

    // Start vtable definition
    vtableStruct->startDefinition();

    // Collect virtual methods in vtable order
    std::vector<const clang::CXXMethodDecl*> virtualMethods = collectVirtualMethods(cxxRecord);

    // Create VtableTypedefGenerator for generating function pointer typedefs
    VtableTypedefGenerator typedefGen(cCtx, ctx.getBuilder());

    // Generate function pointer field for each virtual method
    for (const auto* method : virtualMethods) {
        std::string fieldName;
        clang::QualType funcPtrType;

        // Check if this is a destructor
        if (const auto* dtor = llvm::dyn_cast<clang::CXXDestructorDecl>(method)) {
            fieldName = "destructor";

            // Generate typedef for destructor
            clang::TypedefDecl* typedefDecl = typedefGen.generateTypedefForDestructor(dtor, className);
            if (!typedefDecl) {
                continue; // Skip on error
            }

            // Use the typedef as the field type
            funcPtrType = cCtx.getTypedefType(typedefDecl);
        } else {
            fieldName = method->getNameAsString();

            // Generate typedef for method
            clang::TypedefDecl* typedefDecl = typedefGen.generateTypedef(method, className);
            if (!typedefDecl) {
                continue; // Skip on error
            }

            // Use the typedef as the field type
            funcPtrType = cCtx.getTypedefType(typedefDecl);
        }

        // Create field identifier
        clang::IdentifierInfo& fieldII = cCtx.Idents.get(fieldName);

        // Create function pointer field
        clang::FieldDecl* funcPtrField = clang::FieldDecl::Create(
            cCtx,
            vtableStruct,
            clang::SourceLocation(),
            clang::SourceLocation(),
            &fieldII,
            funcPtrType,
            cCtx.getTrivialTypeSourceInfo(funcPtrType),
            nullptr, // No bitwidth
            false,   // Not mutable
            clang::ICIS_NoInit
        );

        // Add field to vtable struct
        vtableStruct->addDecl(funcPtrField);
    }

    // Complete vtable definition
    vtableStruct->completeDefinition();

    // Add vtable struct to translation unit
    cCtx.getTranslationUnitDecl()->addDecl(vtableStruct);

    return vtableStruct;
}

std::vector<const clang::CXXMethodDecl*> RecordHandler::collectVirtualMethods(
    const clang::CXXRecordDecl* cxxRecord
) {
    std::vector<const clang::CXXMethodDecl*> virtualMethods;

    if (!cxxRecord) {
        return virtualMethods;
    }

    // Use a vector to preserve declaration order, and a map to track which slots are filled
    std::map<std::string, const clang::CXXMethodDecl*> vtableSlotMap;
    std::vector<std::string> slotOrder; // Preserve slot order

    // Step 1: Collect virtual methods from base classes (if any)
    for (const auto& base : cxxRecord->bases()) {
        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        // Recursively collect base class virtual methods
        std::vector<const clang::CXXMethodDecl*> baseMethods = collectVirtualMethods(baseRecord);

        // Add base methods to slots (will be overridden if derived class overrides them)
        // Preserve the order from base class
        for (const auto* baseMethod : baseMethods) {
            std::string methodName;
            if (llvm::isa<clang::CXXDestructorDecl>(baseMethod)) {
                methodName = "destructor";
            } else {
                methodName = baseMethod->getNameAsString();
            }

            // Only add if we haven't seen this slot before
            if (vtableSlotMap.find(methodName) == vtableSlotMap.end()) {
                slotOrder.push_back(methodName);
            }
            vtableSlotMap[methodName] = baseMethod;
        }
    }

    // Step 2: Add/override with this class's virtual methods
    for (const auto* method : cxxRecord->methods()) {
        // Only process virtual methods
        if (!method->isVirtual()) {
            continue;
        }

        std::string methodName;
        if (const auto* dtor = llvm::dyn_cast<clang::CXXDestructorDecl>(method)) {
            methodName = "destructor";
        } else {
            methodName = method->getNameAsString();
        }

        // Add to vtable - either override existing slot or add new slot at end
        if (vtableSlotMap.find(methodName) != vtableSlotMap.end()) {
            // Override existing slot (preserve position in slotOrder)
            vtableSlotMap[methodName] = method;
        } else {
            // New virtual method - add at end
            slotOrder.push_back(methodName);
            vtableSlotMap[methodName] = method;
        }
    }

    // Step 3: Build ordered vector from slot order
    for (const auto& methodName : slotOrder) {
        virtualMethods.push_back(vtableSlotMap[methodName]);
    }

    return virtualMethods;
}

void RecordHandler::injectLpVtblField(
    const clang::CXXRecordDecl* cxxRecord,
    clang::RecordDecl* cRecord,
    HandlerContext& ctx
) {
    // Only inject lpVtbl for polymorphic classes
    if (!cxxRecord || !cxxRecord->isPolymorphic()) {
        return;
    }

    clang::ASTContext& cCtx = ctx.getCContext();
    std::string className = cxxRecord->getNameAsString();

    // Step 1: Create vtable struct type
    // Type: const struct ClassName_vtable *
    std::string vtableName = className + "_vtable";

    // Create identifier for vtable struct
    clang::IdentifierInfo& vtableII = cCtx.Idents.get(vtableName);

    // Create incomplete vtable struct declaration (will be completed by generateVtableStruct)
    // We need to create it here so we can reference it in the pointer type
    clang::RecordDecl* vtableStruct = clang::RecordDecl::Create(
        cCtx,
        clang::TagTypeKind::Struct,
        cCtx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &vtableII
    );

    // Create struct type: struct ClassName_vtable
    clang::QualType vtableStructType = cCtx.getRecordType(vtableStruct);

    // Add const qualifier: const struct ClassName_vtable
    clang::QualType constVtableStructType = vtableStructType.withConst();

    // Create pointer type: const struct ClassName_vtable *
    clang::QualType lpVtblType = cCtx.getPointerType(constVtableStructType);

    // Step 2: Create lpVtbl field
    clang::IdentifierInfo& lpVtblII = cCtx.Idents.get("lpVtbl");

    clang::FieldDecl* lpVtblField = clang::FieldDecl::Create(
        cCtx,
        cRecord,
        clang::SourceLocation(),
        clang::SourceLocation(),
        &lpVtblII,
        lpVtblType,
        cCtx.getTrivialTypeSourceInfo(lpVtblType),
        nullptr, // No bitwidth
        false,   // Not mutable
        clang::ICIS_NoInit
    );

    // Step 3: Add lpVtbl as FIRST field (COM/DCOM ABI requirement)
    // This MUST be done before other fields are added
    cRecord->addDecl(lpVtblField);
}

clang::VarDecl* RecordHandler::generateVtableInstance(
    const clang::CXXRecordDecl* cxxRecord,
    HandlerContext& ctx
) {
    // Only generate vtable instance for polymorphic classes
    if (!cxxRecord || !cxxRecord->isPolymorphic()) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();
    std::string className = cxxRecord->getNameAsString();
    std::string vtableName = className + "_vtable";
    std::string vtableInstanceName = className + "_vtable_instance";

    // Step 1: Find the vtable struct that was already generated
    clang::RecordDecl* vtableStruct = nullptr;
    auto* TU = cCtx.getTranslationUnitDecl();

    for (auto* D : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
            if (RD->getNameAsString() == vtableName) {
                vtableStruct = RD;
                break;
            }
        }
    }

    if (!vtableStruct) {
        // Vtable struct not found - this is an error
        return nullptr;
    }

    // Step 2: Create the vtable struct type
    clang::QualType vtableStructType = cCtx.getRecordType(vtableStruct);

    // Step 3: Make it const
    clang::QualType constVtableStructType = vtableStructType;
    constVtableStructType.addConst();

    // Step 4: Collect virtual methods in vtable order
    std::vector<const clang::CXXMethodDecl*> virtualMethods = collectVirtualMethods(cxxRecord);

    // Step 5: Create initializer list with designated initializers
    std::vector<clang::Expr*> initExprs;
    std::vector<clang::FieldDecl*> initFields;

    // Match virtual methods with vtable struct fields
    unsigned fieldIndex = 0;
    for (auto it = vtableStruct->field_begin(); it != vtableStruct->field_end(); ++it, ++fieldIndex) {
        clang::FieldDecl* field = *it;

        if (fieldIndex >= virtualMethods.size()) {
            break; // Safety check
        }

        const clang::CXXMethodDecl* method = virtualMethods[fieldIndex];

        // Create function name for the translated method
        std::string funcName;
        if (llvm::isa<clang::CXXDestructorDecl>(method)) {
            funcName = className + "_destructor";
        } else {
            funcName = className + "_" + method->getNameAsString();
        }

        // Step 6: Look up the translated function in the C context
        clang::FunctionDecl* funcDecl = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
                if (FD->getNameAsString() == funcName) {
                    funcDecl = FD;
                    break;
                }
            }
        }

        // If function not found, create a placeholder DeclRefExpr with nullptr
        // This allows the AST to be created even if methods haven't been translated yet
        clang::Expr* funcRef = nullptr;

        if (funcDecl) {
            // Create DeclRefExpr to the function
            clang::DeclRefExpr* declRef = clang::DeclRefExpr::Create(
                cCtx,
                clang::NestedNameSpecifierLoc(),
                clang::SourceLocation(),
                funcDecl,
                false, // Not part of template
                clang::SourceLocation(),
                funcDecl->getType(),
                clang::VK_PRValue
            );

            // Implicit cast to function pointer type
            funcRef = clang::ImplicitCastExpr::Create(
                cCtx,
                field->getType(),
                clang::CK_FunctionToPointerDecay,
                declRef,
                nullptr,
                clang::VK_PRValue,
                clang::FPOptionsOverride()
            );
        } else {
            // Create NULL pointer as placeholder
            funcRef = clang::IntegerLiteral::Create(
                cCtx,
                llvm::APInt(cCtx.getTypeSize(cCtx.VoidPtrTy), 0),
                cCtx.VoidPtrTy,
                clang::SourceLocation()
            );
        }

        initExprs.push_back(funcRef);
        initFields.push_back(field);
    }

    // Step 7: Create InitListExpr with designated initializers
    clang::InitListExpr* initList = new (cCtx) clang::InitListExpr(
        cCtx,
        clang::SourceLocation(),
        initExprs,
        clang::SourceLocation()
    );

    // Set designated initializers
    for (size_t i = 0; i < initFields.size(); ++i) {
        initList->setInit(i, initExprs[i]);
    }

    initList->setType(constVtableStructType);
    initList->setSyntacticForm(initList);

    // Step 8: Create VarDecl for the vtable instance
    clang::IdentifierInfo& vtableInstanceII = cCtx.Idents.get(vtableInstanceName);

    clang::VarDecl* vtableInstance = clang::VarDecl::Create(
        cCtx,
        TU, // Parent DeclContext
        clang::SourceLocation(),
        clang::SourceLocation(),
        &vtableInstanceII,
        constVtableStructType,
        cCtx.getTrivialTypeSourceInfo(constVtableStructType),
        clang::SC_Static // Static storage
    );

    // Step 9: Set the initializer
    vtableInstance->setInit(initList);

    // Step 10: Add to translation unit
    TU->addDecl(vtableInstance);

    return vtableInstance;
}


} // namespace cpptoc
