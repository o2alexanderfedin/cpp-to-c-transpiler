/**
 * @file ConstructorHandler.cpp
 * @brief Implementation of ConstructorHandler dispatcher pattern
 *
 * Translates C++ constructors to C initialization functions.
 * Handles vtable initialization, base constructor calls, and parameter translation.
 */

#include "dispatch/ConstructorHandler.h"
#include "dispatch/RecordHandler.h"
#include "CNodeBuilder.h"
#include "MultipleInheritanceAnalyzer.h"
#include "VirtualInheritanceAnalyzer.h"
#include "ConstructorSplitter.h"
#include "VTTGenerator.h"
#include "NameMangler.h"
#include "mapping/DeclMapper.h"
#include "mapping/PathMapper.h"
#include "SourceLocationMapper.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/RecordLayout.h"
#include "llvm/Support/Casting.h"
#include <cassert>

namespace cpptoc {

/**
 * @brief Calculate offset of base subobject in C struct using stored field offsets
 *
 * Finds the first field from the base class in the complete C struct and returns
 * its offset (which was previously stored by RecordHandler during struct generation).
 *
 * @param baseClass C++ base class record
 * @param parentCStruct C struct representing the complete object
 * @param disp Dispatcher (to access FieldOffsetMapper)
 * @return Offset in bytes, or 0 if not found
 */
static unsigned calculateBaseSubobjectOffset(
    const clang::CXXRecordDecl* baseClass,
    clang::RecordDecl* parentCStruct,
    const CppToCVisitorDispatcher& disp
) {
    if (!baseClass || !parentCStruct) return 0;

    // Get the FieldOffsetMapper
    cpptoc::FieldOffsetMapper& offsetMapper = disp.getFieldOffsetMapper();

    // Strategy: Find ANY field from the base class in the parent C struct
    // The first field from baseClass will be at the base subobject's offset

    // Get fields from base class
    if (!baseClass->getDefinition()) return 0;

    for (auto* baseField : baseClass->fields()) {
        std::string fieldName = baseField->getNameAsString();

        // Check if this field exists in parent C struct with stored offset
        if (offsetMapper.hasFieldOffset(parentCStruct, fieldName)) {
            unsigned offset = offsetMapper.getFieldOffset(parentCStruct, fieldName);
            llvm::outs() << "[ConstructorHandler] Found base subobject offset for "
                         << baseClass->getNameAsString() << " via field '" << fieldName
                         << "' at offset " << offset << " bytes\n";
            return offset;
        }
    }

    llvm::outs() << "[ConstructorHandler] WARNING: Could not find offset for base "
                 << baseClass->getNameAsString() << " in struct "
                 << parentCStruct->getNameAsString() << ", using 0\n";
    return 0;
}

void ConstructorHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &ConstructorHandler::canHandle,
        &ConstructorHandler::handleConstructor
    );
}

bool ConstructorHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");
    return llvm::isa<clang::CXXConstructorDecl>(D);
}

void ConstructorHandler::handleConstructor(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(llvm::isa<clang::CXXConstructorDecl>(D) && "Must be CXXConstructorDecl");

    const auto* ctor = llvm::cast<clang::CXXConstructorDecl>(D);

    // Get parent class
    const auto* parentClass = ctor->getParent();
    if (!parentClass) {
        return; // Should never happen
    }

    std::string className = parentClass->getNameAsString();

    // Debug: Log constructor being processed
    std::string ctorName = cpptoc::mangle_constructor(ctor);
    bool isImplicit = ctor->isImplicit();
    bool isDefaultConstructor = ctor->isDefaultConstructor();
    llvm::outs() << "[ConstructorHandler] Processing constructor: " << ctorName
                 << " (implicit=" << (isImplicit ? "yes" : "no")
                 << ", default=" << (isDefaultConstructor ? "yes" : "no")
                 << ")\n";

    // Check if class hierarchy has virtual bases (Task 6)
    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(parentClass);

    bool needsC1C2Split = false;
    // Check if ANY class in hierarchy has virtual bases
    for (const auto& base : parentClass->bases()) {
        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (baseRecord) {
            viAnalyzer.analyzeClass(baseRecord);
            if (viAnalyzer.hasVirtualBases(baseRecord)) {
                needsC1C2Split = true;
                break;
            }
        }
    }

    if (viAnalyzer.hasVirtualBases(parentClass)) {
        needsC1C2Split = true;
    }

    if (needsC1C2Split) {
        llvm::outs() << "[ConstructorHandler] Class " << className
                     << " needs C1/C2 splitting (has virtual bases)\n";
    }

    // Phase 3: For classes with virtual inheritance, generate ONLY C1/C2 constructors (no regular constructor)
    // Per Itanium C++ ABI, C1 is the complete-object constructor, C2 is base-subobject constructor
    if (needsConstructorVariants(ctor)) {
        llvm::outs() << "[ConstructorHandler] Class " << className
                     << " needs C1/C2 constructor variants - skipping regular constructor\n";

        // Generate C1 (complete-object) constructor
        llvm::outs() << "[ConstructorHandler] About to call generateC1Constructor\n";
        llvm::outs().flush();
        generateC1Constructor(ctor, cppASTContext, cASTContext, disp);
        llvm::outs() << "[ConstructorHandler] Returned from generateC1Constructor\n";
        llvm::outs().flush();

        // Generate C2 (base-subobject) constructor
        llvm::outs() << "[ConstructorHandler] About to call generateC2Constructor\n";
        llvm::outs().flush();
        generateC2Constructor(ctor, cppASTContext, cASTContext, disp);
        llvm::outs() << "[ConstructorHandler] Returned from generateC2Constructor\n";
        llvm::outs().flush();

        llvm::outs() << "[ConstructorHandler] About to return from handleConstructor\n";
        llvm::outs().flush();
        return; // Skip regular constructor generation
    }

    // Generate mangled function name using NameMangler API
    std::string funcName = cpptoc::mangle_constructor(ctor);

    // Find C RecordDecl (created by RecordHandler)
    // IMPORTANT: Use PathMapper to get the correct TU for this file, not the global TU
    std::string targetPathForStruct = disp.getCurrentTargetPath();
    if (targetPathForStruct.empty()) {
        targetPathForStruct = disp.getTargetPath(cppASTContext, D);
    }
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPathForStruct);

    clang::RecordDecl* cRecordDecl = nullptr;
    for (auto* decl : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (RD->getName() == className) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        // RecordHandler should have created the struct already
        llvm::outs() << "[ConstructorHandler] ERROR: Could not find C struct for class: "
                     << className << " in TU " << targetPathForStruct
                     << " (has " << std::distance(TU->decls_begin(), TU->decls_end())
                     << " declarations)\n";
        return;
    }

    // Get valid SourceLocation for C AST nodes (needed early for this parameter)
    std::string targetPathForThis = disp.getCurrentTargetPath();
    if (targetPathForThis.empty()) {
        targetPathForThis = disp.getTargetPath(cppASTContext, D);
    }
    SourceLocationMapper& locMapperForThis = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLocForThis = locMapperForThis.getStartOfFile(targetPathForThis);

    // Create 'this' parameter
    clang::QualType classType = cASTContext.getRecordType(cRecordDecl);
    clang::ParmVarDecl* thisParam = createThisParameter(classType, cASTContext, targetLocForThis);

    // Translate constructor parameters
    std::vector<clang::ParmVarDecl*> ctorParams = translateParameters(ctor, disp, cppASTContext, cASTContext);

    // Combine 'this' parameter with constructor parameters
    std::vector<clang::ParmVarDecl*> allParams;
    allParams.push_back(thisParam);
    allParams.insert(allParams.end(), ctorParams.begin(), ctorParams.end());

    // Build constructor body
    // Order (Phase 46 Group 3):
    // Task 8: Base constructor calls MUST be FIRST (they initialize base vtables)
    // Task 7: Then lpVtbl initialization (override base vtables with derived vtables)
    // Then: Member initializers
    std::vector<clang::Stmt*> bodyStmts;

    // Add base constructor calls FIRST (Task 8)
    auto baseCtorCalls = generateBaseConstructorCalls(ctor, thisParam, disp, cppASTContext, cASTContext);
    bodyStmts.insert(bodyStmts.end(), baseCtorCalls.begin(), baseCtorCalls.end());

    // Add lpVtbl initialization(s) AFTER base constructors (Task 7)
    if (parentClass->isPolymorphic()) {
        auto lpVtblInitStmts = injectLpVtblInit(parentClass, thisParam, cppASTContext, cASTContext, targetLocForThis);
        bodyStmts.insert(bodyStmts.end(), lpVtblInitStmts.begin(), lpVtblInitStmts.end());
    }

    // Add member initializer list translations
    // Translate each member initializer (e.g., : field(value)) to this->field = value;
    for (const auto* init : ctor->inits()) {
        if (!init->isWritten() || init->isBaseInitializer()) {
            continue; // Skip compiler-generated and base initializers (already handled)
        }

        if (init->isMemberInitializer()) {
            clang::FieldDecl* field = init->getMember();
            clang::Expr* initExpr = init->getInit();

            if (!field || !initExpr) continue;

            // Find the corresponding C field in the C struct
            clang::FieldDecl* cField = nullptr;
            for (auto* f : cRecordDecl->fields()) {
                if (f->getNameAsString() == field->getNameAsString()) {
                    cField = f;
                    break;
                }
            }

            if (!cField) continue;

            // Create this->field member expression
            clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
                cASTContext,
                clang::NestedNameSpecifierLoc(),
                targetLocForThis,
                thisParam,
                false,
                targetLocForThis,
                thisParam->getType(),
                clang::VK_LValue
            );

            clang::MemberExpr* memberExpr = clang::MemberExpr::CreateImplicit(
                cASTContext,
                thisExpr,
                true, // isArrow (this is a pointer)
                cField,
                cField->getType(),
                clang::VK_LValue,
                clang::OK_Ordinary
            );

            // Dispatch the initialization expression to translate it
            bool initHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(initExpr));

            // Retrieve translated init expression from ExprMapper
            cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
            clang::Expr* cInitExpr = exprMapper.getCreated(initExpr);

            if (!cInitExpr) {
                // Fallback: if expr not translated, try to create simple literal for integer types
                if (const auto* intLit = llvm::dyn_cast<clang::IntegerLiteral>(initExpr)) {
                    cInitExpr = clang::IntegerLiteral::Create(
                        cASTContext,
                        intLit->getValue(),
                        intLit->getType(),
                        targetLocForThis
                    );
                }
            }

            if (cInitExpr) {
                // Create assignment: this->field = value
                clang::BinaryOperator* assignExpr = clang::BinaryOperator::Create(
                    cASTContext,
                    memberExpr,
                    cInitExpr,
                    clang::BO_Assign,
                    cField->getType(),
                    clang::VK_LValue,
                    clang::OK_Ordinary,
                    targetLocForThis,
                    clang::FPOptionsOverride()
                );

                bodyStmts.push_back(assignExpr);
            }
        }
    }

    // Create CompoundStmt (constructor body) using the same targetLoc
    clang::CompoundStmt* body = clang::CompoundStmt::Create(
        cASTContext,
        bodyStmts,
        clang::FPOptionsOverride(),
        targetLocForThis,
        targetLocForThis
    );

    // Create C function using CNodeBuilder
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        funcName,
        cASTContext.VoidTy,
        allParams,
        body
    );

    assert(cFunc && "Failed to create C FunctionDecl for constructor");

    // Register mapping
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    declMapper.setCreated(ctor, cFunc);

    // Get target path and add to C TranslationUnit
    // Note: pathMapper already obtained earlier (line 92), reuse it
    std::string targetPath = disp.getCurrentTargetPath();  // Use current path set by TranslationUnitHandler
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, D);
    }
    clang::TranslationUnitDecl* cTargetTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTargetTU && "Failed to get/create C TranslationUnit");

    cFunc->setDeclContext(cTargetTU);
    cTargetTU->addDecl(cFunc);
    pathMapper.setNodeLocation(cFunc, targetPath);

    // Register parameter mappings
    for (size_t i = 0; i < ctor->getNumParams(); ++i) {
        const auto* cppParam = ctor->getParamDecl(i);
        // Index i+1 because allParams[0] is 'this'
        if (i + 1 < allParams.size()) {
            declMapper.setCreated(cppParam, allParams[i + 1]);
        }
    }

}

std::vector<clang::ParmVarDecl*> ConstructorHandler::translateParameters(
    const clang::CXXConstructorDecl* ctor,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::ParmVarDecl*> cParams;

    // Get valid SourceLocation for C AST nodes
    clang::SourceLocation targetLoc = disp.getTargetSourceLocation(cppASTContext, ctor);

    for (const auto* cppParam : ctor->parameters()) {
        clang::IdentifierInfo& II = cASTContext.Idents.get(cppParam->getNameAsString());
        clang::QualType cppParamType = cppParam->getType();
        clang::QualType cParamType = translateType(cppParamType, cASTContext);

        clang::ParmVarDecl* cParam = clang::ParmVarDecl::Create(
            cASTContext,
            cASTContext.getTranslationUnitDecl(),
            targetLoc,
            targetLoc,
            &II,
            cParamType,
            cASTContext.getTrivialTypeSourceInfo(cParamType),
            clang::SC_None,
            nullptr
        );

        cParams.push_back(cParam);
    }

    return cParams;
}

clang::ParmVarDecl* ConstructorHandler::createThisParameter(
    clang::QualType recordType,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    clang::IdentifierInfo& II = cASTContext.Idents.get("this");
    clang::QualType thisType = cASTContext.getPointerType(recordType);

    return clang::ParmVarDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &II,
        thisType,
        cASTContext.getTrivialTypeSourceInfo(thisType),
        clang::SC_None,
        nullptr
    );
}

clang::QualType ConstructorHandler::translateType(
    clang::QualType cppType,
    clang::ASTContext& cASTContext
) {
    // Check for lvalue reference (T&)
    if (const auto* lvalRefType = llvm::dyn_cast<clang::LValueReferenceType>(cppType.getTypePtr())) {
        clang::QualType pointeeType = lvalRefType->getPointeeType();
        return cASTContext.getPointerType(pointeeType);
    }

    // Check for rvalue reference (T&&)
    if (const auto* rvalRefType = llvm::dyn_cast<clang::RValueReferenceType>(cppType.getTypePtr())) {
        clang::QualType pointeeType = rvalRefType->getPointeeType();
        return cASTContext.getPointerType(pointeeType);
    }

    return cppType;
}

std::vector<clang::Stmt*> ConstructorHandler::injectLpVtblInit(
    const clang::CXXRecordDecl* parentClass,
    clang::ParmVarDecl* thisParam,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    std::vector<clang::Stmt*> stmts;

    if (!parentClass || !parentClass->isPolymorphic()) {
        return stmts;
    }

    std::string className = parentClass->getNameAsString();

    // Use MultipleInheritanceAnalyzer to identify all polymorphic bases
    // Note: const_cast needed because MultipleInheritanceAnalyzer doesn't modify context (only reads)
    MultipleInheritanceAnalyzer miAnalyzer(const_cast<clang::ASTContext&>(cppASTContext));
    auto bases = miAnalyzer.analyzePolymorphicBases(parentClass);

    bool isBaseClassWithNoBases = bases.empty() && parentClass->getNumBases() == 0;

    // Find the C struct
    clang::RecordDecl* cRecordDecl = nullptr;
    auto* TU = cASTContext.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
            if (RD->getName() == className) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        return stmts;
    }

    // Generate initialization statement for each polymorphic base
    for (const auto& baseInfo : bases) {
        std::string baseName = baseInfo.BaseDecl->getNameAsString();
        std::string lpVtblFieldName = baseInfo.VtblFieldName;

        // Find the lpVtbl field in C struct
        clang::FieldDecl* lpVtblField = nullptr;
        for (auto* field : cRecordDecl->fields()) {
            if (field->getNameAsString() == lpVtblFieldName) {
                lpVtblField = field;
                break;
            }
        }

        if (!lpVtblField) {
            continue;
        }

        // Create LHS: this->lpVtbl
        clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
            cASTContext,
            clang::NestedNameSpecifierLoc(),
            targetLoc,
            thisParam,
            false,
            targetLoc,
            thisParam->getType(),
            clang::VK_LValue
        );

        clang::MemberExpr* lpVtblMemberExpr = clang::MemberExpr::Create(
            cASTContext,
            thisExpr,
            true,  // isArrow
            targetLoc,
            clang::NestedNameSpecifierLoc(),
            targetLoc,
            lpVtblField,
            clang::DeclAccessPair::make(lpVtblField, clang::AS_public),
            clang::DeclarationNameInfo(lpVtblField->getDeclName(), targetLoc),
            nullptr,
            lpVtblField->getType(),
            clang::VK_LValue,
            clang::OK_Ordinary,
            clang::NOUR_None
        );

        // Create RHS: &ClassName_BaseName_vtable_instance
        std::string mangledClassName = cpptoc::mangle_class(parentClass);
        std::string vtableInstanceName;
        if (bases.size() == 1 && baseInfo.IsPrimary) {
            vtableInstanceName = mangledClassName + "_vtable_instance";
        } else {
            vtableInstanceName = mangledClassName + "_" + baseName + "_vtable_instance";
        }

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
            std::string vtableStructName;
            if (bases.size() == 1 && baseInfo.IsPrimary) {
                vtableStructName = mangledClassName + "_vtable";
            } else {
                vtableStructName = mangledClassName + "_" + baseName + "_vtable";
            }

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
                clang::IdentifierInfo& vtableII = cASTContext.Idents.get(vtableStructName);
                vtableStruct = clang::RecordDecl::Create(
                    cASTContext,
                    clang::TagTypeKind::Struct,
                    TU,
                    targetLoc,
                    targetLoc,
                    &vtableII
                );
                vtableStruct->startDefinition();
                vtableStruct->completeDefinition();
            }

            clang::QualType vtableType = cASTContext.getRecordType(vtableStruct);
            clang::QualType constVtableType = cASTContext.getConstType(vtableType);

            clang::IdentifierInfo& instanceII = cASTContext.Idents.get(vtableInstanceName);
            vtableInstanceVar = clang::VarDecl::Create(
                cASTContext,
                TU,
                targetLoc,
                targetLoc,
                &instanceII,
                constVtableType,
                cASTContext.getTrivialTypeSourceInfo(constVtableType),
                clang::SC_Extern
            );

            TU->addDecl(vtableInstanceVar);
        }

        // Create &vtable_instance
        clang::DeclRefExpr* vtableInstanceExpr = clang::DeclRefExpr::Create(
            cASTContext,
            clang::NestedNameSpecifierLoc(),
            targetLoc,
            vtableInstanceVar,
            false,
            targetLoc,
            vtableInstanceVar->getType(),
            clang::VK_LValue
        );

        clang::QualType ptrType = cASTContext.getPointerType(vtableInstanceVar->getType());
        clang::UnaryOperator* addrOfExpr = clang::UnaryOperator::Create(
            cASTContext,
            vtableInstanceExpr,
            clang::UO_AddrOf,
            ptrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            targetLoc,
            false,
            clang::FPOptionsOverride()
        );

        // Create assignment: this->lpVtbl = &ClassName_BaseName_vtable_instance
        clang::BinaryOperator* assignExpr = clang::BinaryOperator::Create(
            cASTContext,
            lpVtblMemberExpr,
            addrOfExpr,
            clang::BO_Assign,
            lpVtblField->getType(),
            clang::VK_LValue,
            clang::OK_Ordinary,
            targetLoc,
            clang::FPOptionsOverride()
        );

        stmts.push_back(assignExpr);
    }

    // Handle base class with no bases (single inheritance root)
    if (isBaseClassWithNoBases) {
        clang::FieldDecl* lpVtblField = nullptr;
        for (auto* field : cRecordDecl->fields()) {
            if (field->getNameAsString() == "lpVtbl") {
                lpVtblField = field;
                break;
            }
        }

        if (lpVtblField) {
            clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
                cASTContext,
                clang::NestedNameSpecifierLoc(),
                targetLoc,
                thisParam,
                false,
                targetLoc,
                thisParam->getType(),
                clang::VK_LValue
            );

            clang::MemberExpr* lpVtblMemberExpr = clang::MemberExpr::Create(
                cASTContext,
                thisExpr,
                true,
                targetLoc,
                clang::NestedNameSpecifierLoc(),
                targetLoc,
                lpVtblField,
                clang::DeclAccessPair::make(lpVtblField, clang::AS_public),
                clang::DeclarationNameInfo(lpVtblField->getDeclName(), targetLoc),
                nullptr,
                lpVtblField->getType(),
                clang::VK_LValue,
                clang::OK_Ordinary,
                clang::NOUR_None
            );

            std::string mangledClassName = cpptoc::mangle_class(parentClass);
            std::string vtableInstanceName = mangledClassName + "_vtable_instance";

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
                std::string vtableStructName = mangledClassName + "_vtable";
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
                    clang::IdentifierInfo& vtableII = cASTContext.Idents.get(vtableStructName);
                    vtableStruct = clang::RecordDecl::Create(
                        cASTContext,
                        clang::TagTypeKind::Struct,
                        TU,
                        targetLoc,
                        targetLoc,
                        &vtableII
                    );
                    vtableStruct->startDefinition();
                    vtableStruct->completeDefinition();
                }

                clang::QualType vtableType = cASTContext.getRecordType(vtableStruct);
                clang::QualType constVtableType = cASTContext.getConstType(vtableType);

                clang::IdentifierInfo& instanceII = cASTContext.Idents.get(vtableInstanceName);
                vtableInstanceVar = clang::VarDecl::Create(
                    cASTContext,
                    TU,
                    targetLoc,
                    targetLoc,
                    &instanceII,
                    constVtableType,
                    cASTContext.getTrivialTypeSourceInfo(constVtableType),
                    clang::SC_Extern
                );

                TU->addDecl(vtableInstanceVar);
            }

            clang::DeclRefExpr* vtableInstanceExpr = clang::DeclRefExpr::Create(
                cASTContext,
                clang::NestedNameSpecifierLoc(),
                targetLoc,
                vtableInstanceVar,
                false,
                targetLoc,
                vtableInstanceVar->getType(),
                clang::VK_LValue
            );

            clang::QualType ptrType = cASTContext.getPointerType(vtableInstanceVar->getType());
            clang::UnaryOperator* addrOfExpr = clang::UnaryOperator::Create(
                cASTContext,
                vtableInstanceExpr,
                clang::UO_AddrOf,
                ptrType,
                clang::VK_PRValue,
                clang::OK_Ordinary,
                targetLoc,
                false,
                clang::FPOptionsOverride()
            );

            clang::BinaryOperator* assignExpr = clang::BinaryOperator::Create(
                cASTContext,
                lpVtblMemberExpr,
                addrOfExpr,
                clang::BO_Assign,
                lpVtblField->getType(),
                clang::VK_LValue,
                clang::OK_Ordinary,
                targetLoc,
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
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::Stmt*> calls;

    const auto* parentClass = ctor->getParent();
    if (!parentClass) {
        return calls;
    }

    // Get valid SourceLocation for C AST nodes
    clang::SourceLocation targetLoc = disp.getTargetSourceLocation(cppASTContext, ctor);

    // Get target path for PathMapper TU lookup
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, ctor);
    }

    // Get the C struct for parent class (to calculate base subobject offsets)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    clang::RecordDecl* parentCStruct = nullptr;
    if (declMapper.hasCreated(parentClass)) {
        parentCStruct = llvm::cast<clang::RecordDecl>(declMapper.getCreated(parentClass));
    }

    // Check if parent class has virtual bases (direct or indirect)
    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(parentClass);
    bool hasVirtualBases = viAnalyzer.hasVirtualBases(parentClass);

    if (hasVirtualBases) {
        // CRITICAL: When the derived class has virtual bases, it acts like a C1 constructor:
        // 1. Initialize virtual bases FIRST (most-derived class responsibility)
        // 2. Call C2 (base-subobject) variants for non-virtual bases (they skip virtual base init)

        // Step 1: Initialize all virtual bases directly
        std::set<const clang::CXXRecordDecl*> allVirtualBases;
        std::function<void(const clang::CXXRecordDecl*)> collectVirtualBases;
        collectVirtualBases = [&](const clang::CXXRecordDecl* record) {
            for (const auto& base : record->bases()) {
                if (base.isVirtual()) {
                    const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
                    if (baseRecord && allVirtualBases.insert(baseRecord).second) {
                        collectVirtualBases(baseRecord);
                    }
                }
            }
            // Also collect indirect virtual bases from non-virtual bases
            for (const auto& base : record->bases()) {
                if (!base.isVirtual()) {
                    const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
                    if (baseRecord) {
                        collectVirtualBases(baseRecord);
                    }
                }
            }
        };
        collectVirtualBases(parentClass);

        // Initialize each virtual base (at offset calculated from C struct layout)
        for (const auto* vbase : allVirtualBases) {
            unsigned offset = parentCStruct ? calculateBaseSubobjectOffset(vbase, parentCStruct, disp) : 0;
            clang::CallExpr* call = createBaseConstructorCall(vbase, thisParam, offset, cASTContext, targetLoc);
            if (call) {
                calls.push_back(call);
                llvm::outs() << "[ConstructorHandler] Regular ctor: Initialize virtual base "
                             << vbase->getNameAsString() << "\n";
            }
        }

        // Step 2: Call C2 (base-subobject) variants for non-virtual bases
        unsigned baseIndex = 0;
        for (const auto& base : parentClass->bases()) {
            if (base.isVirtual()) {
                continue; // Already handled above
            }

            const auto* baseClass = base.getType()->getAsCXXRecordDecl();
            if (!baseClass) continue;

            // Determine which constructor variant to call
            std::string variantSuffix = needsConstructorVariants(ctor) && RecordHandler::needsDualLayout(baseClass) ? "_C2" : "";

            // Calculate offset from C struct layout instead of C++ ABI
            unsigned offset = parentCStruct ? calculateBaseSubobjectOffset(baseClass, parentCStruct, disp) : 0;

            clang::CallExpr* call = createBaseConstructorCallVariant(
                baseClass, thisParam, offset, variantSuffix, cASTContext, targetLoc, targetPath, disp, nullptr
            );

            if (call) {
                calls.push_back(call);
                llvm::outs() << "[ConstructorHandler] Regular ctor: Call non-virtual base "
                             << baseClass->getNameAsString() << " with variant " << variantSuffix << "\n";
            }

            baseIndex++;
        }
    } else {
        // No virtual bases - use simple constructor calls
        unsigned baseIndex = 0;
        for (const auto& base : parentClass->bases()) {
            const auto* baseClass = base.getType()->getAsCXXRecordDecl();
            if (!baseClass) continue;

            // Calculate offset from C struct layout instead of C++ ABI
            unsigned offset = parentCStruct ? calculateBaseSubobjectOffset(baseClass, parentCStruct, disp) : 0;

            clang::CallExpr* call = createBaseConstructorCall(baseClass, thisParam, offset, cASTContext, targetLoc);
            if (call) {
                calls.push_back(call);
            }

            baseIndex++;
        }
    }

    return calls;
}

clang::CallExpr* ConstructorHandler::createBaseConstructorCall(
    const clang::CXXRecordDecl* baseClass,
    clang::ParmVarDecl* thisParam,
    unsigned offset,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    std::string baseName = baseClass->getNameAsString();

    // Find the default constructor
    clang::CXXConstructorDecl* baseDefaultCtor = nullptr;
    for (auto* ctor : baseClass->ctors()) {
        if (ctor->isDefaultConstructor()) {
            baseDefaultCtor = ctor;
            break;
        }
    }

    std::string baseCtorName;
    if (baseDefaultCtor) {
        baseCtorName = cpptoc::mangle_constructor(baseDefaultCtor);
    } else {
        baseCtorName = baseName + "_init";
    }

    // Find or create base constructor function declaration
    auto* TU = cASTContext.getTranslationUnitDecl();
    clang::FunctionDecl* baseCtorFunc = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == baseCtorName) {
                baseCtorFunc = FD;
                break;
            }
        }
    }

    if (!baseCtorFunc) {
        // Create forward declaration
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
            clang::IdentifierInfo& II = cASTContext.Idents.get(baseName);
            baseStruct = clang::RecordDecl::Create(
                cASTContext,
                clang::TagTypeKind::Struct,
                TU,
                targetLoc,
                targetLoc,
                &II
            );
            baseStruct->startDefinition();
            baseStruct->completeDefinition();
            TU->addDecl(baseStruct);
        }

        clang::QualType baseType = cASTContext.getRecordType(baseStruct);
        clang::QualType basePtrType = cASTContext.getPointerType(baseType);

        clang::IdentifierInfo& thisII = cASTContext.Idents.get("this");
        clang::ParmVarDecl* baseThisParam = clang::ParmVarDecl::Create(
            cASTContext,
            TU,
            targetLoc,
            targetLoc,
            &thisII,
            basePtrType,
            cASTContext.getTrivialTypeSourceInfo(basePtrType),
            clang::SC_None,
            nullptr
        );

        clang::IdentifierInfo& funcII = cASTContext.Idents.get(baseCtorName);
        baseCtorFunc = clang::FunctionDecl::Create(
            cASTContext,
            TU,
            targetLoc,
            targetLoc,
            clang::DeclarationName(&funcII),
            cASTContext.VoidTy,
            cASTContext.getTrivialTypeSourceInfo(cASTContext.VoidTy),
            clang::SC_None
        );

        baseCtorFunc->setParams({baseThisParam});
        TU->addDecl(baseCtorFunc);
    }

    // Create argument expression
    clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        thisParam,
        false,
        targetLoc,
        thisParam->getType(),
        clang::VK_LValue
    );

    clang::Expr* adjustedThis = thisExpr;

    // Add offset for non-primary base
    if (offset > 0) {
        clang::QualType charPtrType = cASTContext.getPointerType(cASTContext.CharTy);
        clang::CStyleCastExpr* charCast = clang::CStyleCastExpr::Create(
            cASTContext,
            charPtrType,
            clang::VK_PRValue,
            clang::CK_BitCast,
            thisExpr,
            nullptr,
            clang::FPOptionsOverride(),
            cASTContext.getTrivialTypeSourceInfo(charPtrType),
            targetLoc,
            targetLoc
        );

        llvm::APInt offsetValue(32, offset);
        clang::IntegerLiteral* offsetLit = clang::IntegerLiteral::Create(
            cASTContext,
            offsetValue,
            cASTContext.IntTy,
            targetLoc
        );

        clang::BinaryOperator* addExpr = clang::BinaryOperator::Create(
            cASTContext,
            charCast,
            offsetLit,
            clang::BO_Add,
            charPtrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            targetLoc,
            clang::FPOptionsOverride()
        );

        adjustedThis = addExpr;
    }

    // Cast to base pointer type
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
        return nullptr;
    }

    clang::QualType baseType = cASTContext.getRecordType(baseStruct);
    clang::QualType basePtrType = cASTContext.getPointerType(baseType);

    clang::CStyleCastExpr* baseCast = clang::CStyleCastExpr::Create(
        cASTContext,
        basePtrType,
        clang::VK_PRValue,
        clang::CK_BitCast,
        adjustedThis,
        nullptr,
        clang::FPOptionsOverride(),
        cASTContext.getTrivialTypeSourceInfo(basePtrType),
        targetLoc,
        targetLoc
    );

    // Create CallExpr
    std::vector<clang::Expr*> args = {baseCast};

    clang::CallExpr* callExpr = clang::CallExpr::Create(
        cASTContext,
        clang::DeclRefExpr::Create(
            cASTContext,
            clang::NestedNameSpecifierLoc(),
            targetLoc,
            baseCtorFunc,
            false,
            targetLoc,
            baseCtorFunc->getType(),
            clang::VK_LValue
        ),
        args,
        cASTContext.VoidTy,
        clang::VK_PRValue,
        targetLoc,
        clang::FPOptionsOverride()
    );

    return callExpr;
}

clang::CallExpr* ConstructorHandler::createBaseConstructorCallVariant(
    const clang::CXXRecordDecl* baseClass,
    clang::ParmVarDecl* thisParam,
    unsigned offset,
    const std::string& variantSuffix,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc,
    const std::string& targetPath,
    const CppToCVisitorDispatcher& disp,
    clang::ParmVarDecl* vttParam
) {
    llvm::outs() << "[createBaseConstructorCallVariant] ENTRY: baseClass=" << (baseClass ? baseClass->getNameAsString() : "NULL")
                 << ", offset=" << offset << ", variantSuffix='" << variantSuffix << "'\n";
    llvm::outs().flush();

    std::string baseName = baseClass->getNameAsString();
    llvm::outs() << "[createBaseConstructorCallVariant] baseName=" << baseName << "\n";
    llvm::outs().flush();

    // Find the default constructor
    llvm::outs() << "[createBaseConstructorCallVariant] Looking for default constructor\n";
    llvm::outs().flush();
    clang::CXXConstructorDecl* baseDefaultCtor = nullptr;
    for (auto* ctor : baseClass->ctors()) {
        if (ctor->isDefaultConstructor()) {
            baseDefaultCtor = ctor;
            llvm::outs() << "[createBaseConstructorCallVariant] Found default constructor\n";
            llvm::outs().flush();
            break;
        }
    }
    llvm::outs() << "[createBaseConstructorCallVariant] Default constructor search complete\n";
    llvm::outs().flush();

    std::string baseCtorName;
    if (baseDefaultCtor) {
        baseCtorName = cpptoc::mangle_constructor(baseDefaultCtor) + variantSuffix;
    } else {
        baseCtorName = baseName + "_init" + variantSuffix;
    }

    // Find or create base constructor function declaration in PathMapper TU
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    auto* TU = pathMapper.getOrCreateTU(targetPath);
    clang::FunctionDecl* baseCtorFunc = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == baseCtorName) {
                baseCtorFunc = FD;
                break;
            }
        }
    }

    if (!baseCtorFunc) {
        // Create forward declaration
        // Determine the struct name based on variant suffix
        std::string baseStructName = baseName;
        if (variantSuffix == "_C2") {
            baseStructName += "__base";
        }

        clang::RecordDecl* baseStruct = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                if (RD->getNameAsString() == baseStructName) {
                    baseStruct = RD;
                    break;
                }
            }
        }

        if (!baseStruct) {
            clang::IdentifierInfo& II = cASTContext.Idents.get(baseStructName);
            baseStruct = clang::RecordDecl::Create(
                cASTContext,
                clang::TagTypeKind::Struct,
                TU,
                targetLoc,
                targetLoc,
                &II
            );
            baseStruct->startDefinition();
            baseStruct->completeDefinition();
            TU->addDecl(baseStruct);
        }

        clang::QualType baseType = cASTContext.getRecordType(baseStruct);
        clang::QualType basePtrType = cASTContext.getPointerType(baseType);

        clang::IdentifierInfo& thisII = cASTContext.Idents.get("this");
        clang::ParmVarDecl* baseThisParam = clang::ParmVarDecl::Create(
            cASTContext,
            TU,
            targetLoc,
            targetLoc,
            &thisII,
            basePtrType,
            cASTContext.getTrivialTypeSourceInfo(basePtrType),
            clang::SC_None,
            nullptr
        );

        // Add parameters: this + VTT (for C1/C2 variants)
        std::vector<clang::ParmVarDecl*> params = {baseThisParam};
        std::vector<clang::QualType> paramTypes = {basePtrType};

        if (variantSuffix == "_C1" || variantSuffix == "_C2") {
            // Add VTT parameter for C1/C2 variants
            clang::QualType vttType = cASTContext.getPointerType(
                cASTContext.getPointerType(cASTContext.getConstType(cASTContext.VoidTy))
            );
            clang::IdentifierInfo& vttII = cASTContext.Idents.get("vtt");
            clang::ParmVarDecl* vttParmDecl = clang::ParmVarDecl::Create(
                cASTContext,
                TU,
                targetLoc,
                targetLoc,
                &vttII,
                vttType,
                cASTContext.getTrivialTypeSourceInfo(vttType),
                clang::SC_None,
                nullptr
            );
            params.push_back(vttParmDecl);
            paramTypes.push_back(vttType);
        }

        // Create proper function prototype type
        clang::FunctionProtoType::ExtProtoInfo EPI;
        clang::QualType funcType = cASTContext.getFunctionType(
            cASTContext.VoidTy,  // Return type
            paramTypes,           // Parameter types
            EPI                   // Extra info
        );

        clang::IdentifierInfo& funcII = cASTContext.Idents.get(baseCtorName);
        baseCtorFunc = clang::FunctionDecl::Create(
            cASTContext,
            TU,
            targetLoc,
            targetLoc,
            clang::DeclarationName(&funcII),
            funcType,
            cASTContext.getTrivialTypeSourceInfo(funcType),
            clang::SC_None
        );

        baseCtorFunc->setParams(params);
        TU->addDecl(baseCtorFunc);
    }

    // Create argument expression
    clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        thisParam,
        false,
        targetLoc,
        thisParam->getType(),
        clang::VK_LValue
    );

    clang::Expr* adjustedThis = thisExpr;

    // Add offset for non-primary base
    if (offset > 0) {
        clang::QualType charPtrType = cASTContext.getPointerType(cASTContext.CharTy);
        clang::CStyleCastExpr* charCast = clang::CStyleCastExpr::Create(
            cASTContext,
            charPtrType,
            clang::VK_PRValue,
            clang::CK_BitCast,
            thisExpr,
            nullptr,
            clang::FPOptionsOverride(),
            cASTContext.getTrivialTypeSourceInfo(charPtrType),
            targetLoc,
            targetLoc
        );

        llvm::APInt offsetValue(32, offset);
        clang::IntegerLiteral* offsetLit = clang::IntegerLiteral::Create(
            cASTContext,
            offsetValue,
            cASTContext.IntTy,
            targetLoc
        );

        clang::BinaryOperator* addExpr = clang::BinaryOperator::Create(
            cASTContext,
            charCast,
            offsetLit,
            clang::BO_Add,
            charPtrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            targetLoc,
            clang::FPOptionsOverride()
        );

        adjustedThis = addExpr;
    }

    // Cast to base pointer type (determine struct name based on variant)
    std::string baseStructName = baseName;
    if (variantSuffix == "_C2") {
        baseStructName += "__base";
    }

    llvm::outs() << "[createBaseConstructorCallVariant] Looking for struct: " << baseStructName << " in TU\n";

    clang::RecordDecl* baseStruct = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
            if (RD->getNameAsString() == baseStructName) {
                baseStruct = RD;
                llvm::outs() << "[createBaseConstructorCallVariant] Found struct: " << baseStructName
                             << " (isCompleteDefinition=" << RD->isCompleteDefinition()
                             << ", field_count=" << std::distance(RD->field_begin(), RD->field_end()) << ")\n";
                break;
            }
        }
    }

    if (!baseStruct) {
        llvm::outs() << "[createBaseConstructorCallVariant] ERROR: Could not find struct " << baseStructName << " in TU\n";
        return nullptr;
    }

    llvm::outs() << "[createBaseConstructorCallVariant] Creating base type for struct: " << baseStructName << "\n";
    llvm::outs() << "[createBaseConstructorCallVariant] baseStruct->getTypeForDecl(): " << (baseStruct->getTypeForDecl() ? "EXISTS" : "NULL") << "\n";
    llvm::outs().flush();

    // Always use ASTContext.getRecordType() to ensure proper type canonicalization
    // This prevents non-canonical types that can cause castAs assertions
    clang::QualType baseType = cASTContext.getRecordType(baseStruct);
    llvm::outs() << "[createBaseConstructorCallVariant] Created canonical RecordType via ASTContext\n";

    llvm::outs() << "[createBaseConstructorCallVariant] Creating pointer type\n";
    clang::QualType basePtrType = cASTContext.getPointerType(baseType);

    llvm::outs() << "[createBaseConstructorCallVariant] Creating cast expression\n";
    llvm::outs() << "[createBaseConstructorCallVariant] adjustedThis type: " << adjustedThis->getType().getAsString() << "\n";
    llvm::outs() << "[createBaseConstructorCallVariant] basePtrType: " << basePtrType.getAsString() << "\n";
    llvm::outs().flush();

    clang::CStyleCastExpr* baseCast = clang::CStyleCastExpr::Create(
        cASTContext,
        basePtrType,
        clang::VK_PRValue,
        clang::CK_BitCast,
        adjustedThis,
        nullptr,
        clang::FPOptionsOverride(),
        cASTContext.getTrivialTypeSourceInfo(basePtrType),
        targetLoc,
        targetLoc
    );
    llvm::outs() << "[createBaseConstructorCallVariant] Cast expression created successfully\n";
    llvm::outs() << "[createBaseConstructorCallVariant] baseCast type: " << baseCast->getType().getAsString() << "\n";
    llvm::outs().flush();

    // Create CallExpr
    std::vector<clang::Expr*> args = {baseCast};

    // Add VTT parameter for C1/C2 variants
    llvm::outs() << "[createBaseConstructorCallVariant] variantSuffix=" << variantSuffix
                 << ", vttParam=" << (vttParam ? "NOT NULL" : "NULL") << "\n";
    llvm::outs().flush();
    if ((variantSuffix == "_C1" || variantSuffix == "_C2") && vttParam) {
        llvm::outs() << "[createBaseConstructorCallVariant] Adding VTT parameter to call\n";
        llvm::outs().flush();
        clang::DeclRefExpr* vttExpr = clang::DeclRefExpr::Create(
            cASTContext,
            clang::NestedNameSpecifierLoc(),
            targetLoc,
            vttParam,
            false,
            targetLoc,
            vttParam->getType(),
            clang::VK_LValue
        );
        args.push_back(vttExpr);
    }

    llvm::outs() << "[createBaseConstructorCallVariant] About to create DeclRefExpr for baseCtorFunc\n";
    llvm::outs() << "[createBaseConstructorCallVariant] baseCtorFunc name: " << baseCtorFunc->getNameAsString() << "\n";
    llvm::outs() << "[createBaseConstructorCallVariant] baseCtorFunc type: " << baseCtorFunc->getType().getAsString() << "\n";
    llvm::outs().flush();

    // Use function type directly (not pointer type) for DeclRefExpr in CallExpr
    clang::DeclRefExpr* funcRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        baseCtorFunc,
        false,
        targetLoc,
        baseCtorFunc->getType(),
        clang::VK_PRValue
    );

    llvm::outs() << "[createBaseConstructorCallVariant] Created DeclRefExpr successfully\n";
    llvm::outs().flush();

    llvm::outs() << "[createBaseConstructorCallVariant] About to create CallExpr\n";
    llvm::outs().flush();

    clang::CallExpr* callExpr = clang::CallExpr::Create(
        cASTContext,
        funcRef,
        args,
        cASTContext.VoidTy,
        clang::VK_PRValue,
        targetLoc,
        clang::FPOptionsOverride()
    );

    llvm::outs() << "[createBaseConstructorCallVariant] Created CallExpr successfully\n";
    llvm::outs().flush();

    return callExpr;
}

// Phase 3: Constructor Variant Generation

// Helper function to translate member initializers into assignment statements
static std::vector<clang::Stmt*> translateMemberInitializers(
    const clang::CXXConstructorDecl* ctor,
    clang::ParmVarDecl* thisParam,
    clang::RecordDecl* cRecordDecl,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    std::vector<clang::Stmt*> stmts;

    for (const auto* init : ctor->inits()) {
        if (!init->isWritten() || init->isBaseInitializer()) {
            continue; // Skip compiler-generated and base initializers
        }

        if (init->isMemberInitializer()) {
            clang::FieldDecl* field = init->getMember();
            clang::Expr* initExpr = init->getInit();

            if (!field || !initExpr) continue;

            // Find the corresponding C field in the C struct
            clang::FieldDecl* cField = nullptr;
            for (auto* f : cRecordDecl->fields()) {
                if (f->getNameAsString() == field->getNameAsString()) {
                    cField = f;
                    break;
                }
            }

            if (!cField) continue;

            // Create this->field member expression
            clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
                cASTContext,
                clang::NestedNameSpecifierLoc(),
                targetLoc,
                thisParam,
                false,
                targetLoc,
                thisParam->getType(),
                clang::VK_LValue
            );

            clang::MemberExpr* memberExpr = clang::MemberExpr::CreateImplicit(
                cASTContext,
                thisExpr,
                true, // isArrow (this is a pointer)
                cField,
                cField->getType(),
                clang::VK_LValue,
                clang::OK_Ordinary
            );

            // Dispatch the initialization expression to translate it
            bool initHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(initExpr));

            // Retrieve translated init expression from ExprMapper
            cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
            clang::Expr* cInitExpr = exprMapper.getCreated(initExpr);

            if (!cInitExpr) {
                // Fallback: if expr not translated, try to create simple literal for integer types
                if (const auto* intLit = llvm::dyn_cast<clang::IntegerLiteral>(initExpr)) {
                    cInitExpr = clang::IntegerLiteral::Create(
                        cASTContext,
                        intLit->getValue(),
                        intLit->getType(),
                        targetLoc
                    );
                }
            }

            if (cInitExpr) {
                // Create assignment: this->field = value
                clang::BinaryOperator* assignExpr = clang::BinaryOperator::Create(
                    cASTContext,
                    memberExpr,
                    cInitExpr,
                    clang::BO_Assign,
                    cField->getType(),
                    clang::VK_LValue,
                    clang::OK_Ordinary,
                    targetLoc,
                    clang::FPOptionsOverride()
                );

                stmts.push_back(assignExpr);
            }
        }
    }

    return stmts;
}

bool ConstructorHandler::needsConstructorVariants(const clang::CXXConstructorDecl* ctor) {
    if (!ctor) return false;

    const clang::CXXRecordDecl* record = ctor->getParent();

    // Needs variants if class requires dual layout
    // Use RecordHandler::needsDualLayout() for consistency
    return RecordHandler::needsDualLayout(record);
}

void ConstructorHandler::generateC1Constructor(
    const clang::CXXConstructorDecl* ctor,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const CppToCVisitorDispatcher& disp
) {
    if (!ctor) return;

    const clang::CXXRecordDecl* record = ctor->getParent();
    if (!record) return;

    std::string className = record->getNameAsString();

    // Generate C1 constructor name: ClassName_ctor_C1
    std::string c1Name = cpptoc::mangle_constructor(ctor) + "_C1";

    llvm::outs() << "[ConstructorHandler] generateC1Constructor: Starting generation for " << c1Name << "\n";

    // Get target path and source location
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, ctor);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Get or create TU
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);

    // Find the complete-object struct (ClassName)
    clang::RecordDecl* cRecordDecl = nullptr;
    for (auto* decl : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (RD->getName() == className) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        llvm::outs() << "[ConstructorHandler] C1: Could not find complete-object struct: "
                     << className << "\n";
        return;
    }

    // Create 'this' parameter: ClassName* (complete-object layout)
    clang::QualType classType = cASTContext.getRecordType(cRecordDecl);
    clang::ParmVarDecl* thisParam = createThisParameter(classType, cASTContext, targetLoc);

    // Create VTT parameter: const void** vtt
    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(record);

    std::vector<clang::ParmVarDecl*> allParams;
    allParams.push_back(thisParam);

    clang::ParmVarDecl* vttParam = nullptr;
    if (viAnalyzer.needsVTT(record)) {
        clang::IdentifierInfo& vttII = cASTContext.Idents.get("vtt");
        clang::QualType voidPtrType = cASTContext.getPointerType(cASTContext.VoidTy);
        clang::QualType constVoidPtrType = cASTContext.getConstType(voidPtrType);
        clang::QualType vttType = cASTContext.getPointerType(constVoidPtrType);

        vttParam = clang::ParmVarDecl::Create(
            cASTContext,
            TU,
            targetLoc,
            targetLoc,
            &vttII,
            vttType,
            cASTContext.getTrivialTypeSourceInfo(vttType),
            clang::SC_None,
            nullptr
        );
        allParams.push_back(vttParam);
    }

    // Add original constructor parameters
    std::vector<clang::ParmVarDecl*> ctorParams = translateParameters(ctor, disp, cppASTContext, cASTContext);
    allParams.insert(allParams.end(), ctorParams.begin(), ctorParams.end());

    // CRITICAL FIX: Create function declaration FIRST before building body
    // This breaks the circular dependency where CompoundStmtHandler tries to find
    // the C1 constructor while we're still building it
    llvm::outs() << "[ConstructorHandler] generateC1Constructor: Creating function declaration BEFORE body\n";

    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* c1Func = builder.funcDecl(
        c1Name,
        cASTContext.VoidTy,
        allParams,
        nullptr  // No body yet
    );

    assert(c1Func && "Failed to create C1 FunctionDecl");

    // Add function to TU immediately so it can be found during body generation
    c1Func->setDeclContext(TU);
    TU->addDecl(c1Func);
    pathMapper.setNodeLocation(c1Func, targetPath);

    llvm::outs() << "[ConstructorHandler] generateC1Constructor: Function declaration added to TU, now building body\n";

    // Build constructor body
    std::vector<clang::Stmt*> bodyStmts;

    // C1: Initialize virtual bases FIRST (C1 responsibility)
    auto virtualBases = viAnalyzer.getVirtualBases(record);
    for (const auto* vbase : virtualBases) {
        // Virtual bases use C1 constructor (they're complete objects when initialized)
        std::string variantSuffix = RecordHandler::needsDualLayout(vbase) ? "_C1" : "";

        // Calculate offset for virtual base using C struct layout
        // Find the first field from the virtual base in the derived C struct
        unsigned offset = 0;

        // Get the C struct for the virtual base (or __base variant if it has virtual bases)
        clang::RecordDecl* vbaseCStruct = nullptr;
        cpptoc::DeclMapper& declMapper = const_cast<CppToCVisitorDispatcher&>(disp).getDeclMapper();

        if (RecordHandler::needsDualLayout(vbase)) {
            std::string vbaseStructName = cpptoc::mangle_class(vbase) + "__base";
            cpptoc::PathMapper& pathMapper = const_cast<CppToCVisitorDispatcher&>(disp).getPathMapper();
            clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);
            for (auto* decl : TU->decls()) {
                if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
                    if (RD->getName() == vbaseStructName) {
                        vbaseCStruct = RD;
                        break;
                    }
                }
            }
        } else if (declMapper.hasCreated(vbase)) {
            vbaseCStruct = llvm::cast<clang::RecordDecl>(declMapper.getCreated(vbase));
        }

        if (vbaseCStruct && !vbaseCStruct->field_empty()) {
            std::string firstFieldName = vbaseCStruct->field_begin()->getNameAsString();
            const clang::ASTRecordLayout& derivedLayout = cASTContext.getASTRecordLayout(cRecordDecl);
            unsigned fieldIdx = 0;
            for (auto* field : cRecordDecl->fields()) {
                if (field->getNameAsString() == firstFieldName) {
                    uint64_t offsetInBits = derivedLayout.getFieldOffset(fieldIdx);
                    offset = static_cast<unsigned>(offsetInBits / 8);
                    llvm::outs() << "[ConstructorHandler] C1: Virtual base " << vbase->getNameAsString()
                                 << " field '" << firstFieldName << "' found at offset " << offset << " bytes\n";
                    break;
                }
                fieldIdx++;
            }
        }

        // CRITICAL: Only pass VTT parameter to C1/C2 variants, not regular constructors
        clang::ParmVarDecl* vttParamToPass = (variantSuffix == "_C1" || variantSuffix == "_C2") ? vttParam : nullptr;

        clang::CallExpr* call = createBaseConstructorCallVariant(
            vbase, thisParam, offset, variantSuffix, cASTContext, targetLoc, targetPath, disp, vttParamToPass
        );

        if (call) {
            llvm::outs() << "[ConstructorHandler] C1: Adding call to bodyStmts\n";
            llvm::outs().flush();
            bodyStmts.push_back(call);
            llvm::outs() << "[ConstructorHandler] C1: Successfully added call to bodyStmts\n";
            llvm::outs() << "[ConstructorHandler] C1: Initialize virtual base "
                         << vbase->getNameAsString() << " with variant " << variantSuffix << " at offset " << offset << "\n";
            llvm::outs().flush();
        }
    }

    llvm::outs() << "[ConstructorHandler] C1: Finished virtual base initialization, bodyStmts size: " << bodyStmts.size() << "\n";
    llvm::outs().flush();

    // Call non-virtual base constructors (use C2 variants if they have virtual bases)
    unsigned baseIndex = 0;
    for (const auto& base : record->bases()) {
        if (base.isVirtual()) continue; // Skip virtual bases (already handled)

        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        // If base needs dual layout, call C2 (base-subobject constructor)
        // Otherwise, call normal constructor
        std::string variantSuffix = RecordHandler::needsDualLayout(baseRecord) ? "_C2" : "";

        // Calculate offset for non-primary base using C struct layout
        unsigned offset = 0;
        if (baseIndex > 0) {
            // Find the C struct for the base (or __base variant if it has virtual bases)
            clang::RecordDecl* baseCStruct = nullptr;
            cpptoc::DeclMapper& declMapper = const_cast<CppToCVisitorDispatcher&>(disp).getDeclMapper();

            if (RecordHandler::needsDualLayout(baseRecord)) {
                std::string baseStructName = cpptoc::mangle_class(baseRecord) + "__base";
                cpptoc::PathMapper& pathMapper = const_cast<CppToCVisitorDispatcher&>(disp).getPathMapper();
                clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);
                for (auto* decl : TU->decls()) {
                    if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
                        if (RD->getName() == baseStructName) {
                            baseCStruct = RD;
                            break;
                        }
                    }
                }
            } else if (declMapper.hasCreated(baseRecord)) {
                baseCStruct = llvm::cast<clang::RecordDecl>(declMapper.getCreated(baseRecord));
            }

            if (baseCStruct && !baseCStruct->field_empty()) {
                std::string firstFieldName = baseCStruct->field_begin()->getNameAsString();
                const clang::ASTRecordLayout& derivedLayout = cASTContext.getASTRecordLayout(cRecordDecl);
                unsigned fieldIdx = 0;
                for (auto* field : cRecordDecl->fields()) {
                    if (field->getNameAsString() == firstFieldName) {
                        uint64_t offsetInBits = derivedLayout.getFieldOffset(fieldIdx);
                        offset = static_cast<unsigned>(offsetInBits / 8);
                        llvm::outs() << "[ConstructorHandler] C1: Non-virtual base " << baseRecord->getNameAsString()
                                     << " field '" << firstFieldName << "' found at offset " << offset << " bytes\n";
                        break;
                    }
                    fieldIdx++;
                }
            }
        }

        clang::CallExpr* call = createBaseConstructorCallVariant(
            baseRecord, thisParam, offset, variantSuffix, cASTContext, targetLoc, targetPath, disp, vttParam
        );

        if (call) {
            bodyStmts.push_back(call);
            llvm::outs() << "[ConstructorHandler] C1: Call base constructor for "
                         << baseRecord->getNameAsString() << " with variant " << variantSuffix << " at offset " << offset << "\n";
        }

        baseIndex++;
    }

    llvm::outs() << "[ConstructorHandler] C1: About to translate member initializers\n";
    llvm::outs().flush();

    // Add member initialization (cRecordDecl already found at line 1348)
    auto memberInitStmts = translateMemberInitializers(
        ctor, thisParam, cRecordDecl, disp, cppASTContext, cASTContext, targetLoc
    );
    llvm::outs() << "[ConstructorHandler] C1: Translated " << memberInitStmts.size() << " member initializers\n";
    llvm::outs().flush();

    bodyStmts.insert(bodyStmts.end(), memberInitStmts.begin(), memberInitStmts.end());

    llvm::outs() << "[ConstructorHandler] C1: About to inject lpVtbl init (isPolymorphic=" << record->isPolymorphic() << ")\n";
    llvm::outs().flush();

    // Add lpVtbl initialization
    if (record->isPolymorphic()) {
        auto lpVtblInitStmts = injectLpVtblInit(record, thisParam, cppASTContext, cASTContext, targetLoc);
        llvm::outs() << "[ConstructorHandler] C1: Injected " << lpVtblInitStmts.size() << " lpVtbl init statements\n";
        llvm::outs().flush();
        bodyStmts.insert(bodyStmts.end(), lpVtblInitStmts.begin(), lpVtblInitStmts.end());
    }

    llvm::outs() << "[ConstructorHandler] C1: About to create CompoundStmt with " << bodyStmts.size() << " statements\n";
    llvm::outs().flush();

    // Create CompoundStmt
    llvm::outs() << "[ConstructorHandler] C1: Creating CompoundStmt...\n";
    llvm::outs().flush();

    clang::CompoundStmt* body = clang::CompoundStmt::Create(
        cASTContext,
        bodyStmts,
        clang::FPOptionsOverride(),
        targetLoc,
        targetLoc
    );

    llvm::outs() << "[ConstructorHandler] C1: CompoundStmt created successfully\n";
    llvm::outs().flush();

    // Set the body on the function declaration
    llvm::outs() << "[ConstructorHandler] C1: Setting body on function declaration\n";
    llvm::outs().flush();

    c1Func->setBody(body);

    llvm::outs() << "[ConstructorHandler] C1: Body set successfully\n";
    llvm::outs().flush();

    llvm::outs() << "[ConstructorHandler] generateC1Constructor: Successfully generated C1 constructor: " << c1Name << "\n";
}

void ConstructorHandler::generateC2Constructor(
    const clang::CXXConstructorDecl* ctor,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const CppToCVisitorDispatcher& disp
) {
    if (!ctor) return;

    const clang::CXXRecordDecl* record = ctor->getParent();
    if (!record) return;

    std::string className = record->getNameAsString();

    // Generate C2 constructor name: ClassName_ctor_C2
    std::string c2Name = cpptoc::mangle_constructor(ctor) + "_C2";

    // Get target path and source location
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, ctor);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Get or create TU
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);

    // Find the base-subobject struct (ClassName__base)
    std::string baseStructName = className + "__base";
    clang::RecordDecl* cRecordDecl = nullptr;
    for (auto* decl : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (RD->getName() == baseStructName) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        llvm::outs() << "[ConstructorHandler] C2: Could not find base-subobject struct: "
                     << baseStructName << "\n";
        return;
    }

    // Create 'this' parameter: ClassName__base* (base-subobject layout)
    clang::QualType classType = cASTContext.getRecordType(cRecordDecl);
    clang::ParmVarDecl* thisParam = createThisParameter(classType, cASTContext, targetLoc);

    // Create VTT parameter: const void** vtt
    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(record);

    std::vector<clang::ParmVarDecl*> allParams;
    allParams.push_back(thisParam);

    clang::ParmVarDecl* vttParam = nullptr;
    if (viAnalyzer.needsVTT(record)) {
        clang::IdentifierInfo& vttII = cASTContext.Idents.get("vtt");
        clang::QualType voidPtrType = cASTContext.getPointerType(cASTContext.VoidTy);
        clang::QualType constVoidPtrType = cASTContext.getConstType(voidPtrType);
        clang::QualType vttType = cASTContext.getPointerType(constVoidPtrType);

        vttParam = clang::ParmVarDecl::Create(
            cASTContext,
            TU,
            targetLoc,
            targetLoc,
            &vttII,
            vttType,
            cASTContext.getTrivialTypeSourceInfo(vttType),
            clang::SC_None,
            nullptr
        );
        allParams.push_back(vttParam);
    }

    // Add original constructor parameters
    std::vector<clang::ParmVarDecl*> ctorParams = translateParameters(ctor, disp, cppASTContext, cASTContext);
    allParams.insert(allParams.end(), ctorParams.begin(), ctorParams.end());

    // CRITICAL FIX: Create function declaration FIRST before building body
    // This breaks the circular dependency where CompoundStmtHandler tries to find
    // the C2 constructor while we're still building it
    llvm::outs() << "[ConstructorHandler] generateC2Constructor: Creating function declaration BEFORE body\n";

    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* c2Func = builder.funcDecl(
        c2Name,
        cASTContext.VoidTy,
        allParams,
        nullptr  // No body yet
    );

    assert(c2Func && "Failed to create C2 FunctionDecl");

    // Add function to TU immediately so it can be found during body generation
    c2Func->setDeclContext(TU);
    TU->addDecl(c2Func);
    pathMapper.setNodeLocation(c2Func, targetPath);

    llvm::outs() << "[ConstructorHandler] generateC2Constructor: Function declaration added to TU, now building body\n";

    // Build constructor body
    std::vector<clang::Stmt*> bodyStmts;

    // C2: SKIP virtual base initialization (parent's C1 handles it)

    // Call non-virtual base constructors (use C2 variants if they have virtual bases)
    unsigned baseIndex = 0;
    for (const auto& base : record->bases()) {
        if (base.isVirtual()) continue; // Skip virtual bases

        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        // If base needs dual layout, call C2 (base-subobject constructor)
        // Otherwise, call normal constructor
        std::string variantSuffix = RecordHandler::needsDualLayout(baseRecord) ? "_C2" : "";

        // Calculate offset for non-primary base using C struct layout
        unsigned offset = 0;
        if (baseIndex > 0) {
            // Find the C struct for the base (or __base variant if it has virtual bases)
            clang::RecordDecl* baseCStruct = nullptr;
            cpptoc::DeclMapper& declMapper = const_cast<CppToCVisitorDispatcher&>(disp).getDeclMapper();

            if (RecordHandler::needsDualLayout(baseRecord)) {
                std::string baseStructName = cpptoc::mangle_class(baseRecord) + "__base";
                cpptoc::PathMapper& pathMapper = const_cast<CppToCVisitorDispatcher&>(disp).getPathMapper();
                clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);
                for (auto* decl : TU->decls()) {
                    if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
                        if (RD->getName() == baseStructName) {
                            baseCStruct = RD;
                            break;
                        }
                    }
                }
            } else if (declMapper.hasCreated(baseRecord)) {
                baseCStruct = llvm::cast<clang::RecordDecl>(declMapper.getCreated(baseRecord));
            }

            if (baseCStruct && !baseCStruct->field_empty()) {
                std::string firstFieldName = baseCStruct->field_begin()->getNameAsString();
                // Use the base-subobject layout (cRecordDecl) for offset calculation
                const clang::ASTRecordLayout& derivedLayout = cASTContext.getASTRecordLayout(cRecordDecl);
                unsigned fieldIdx = 0;
                for (auto* field : cRecordDecl->fields()) {
                    if (field->getNameAsString() == firstFieldName) {
                        uint64_t offsetInBits = derivedLayout.getFieldOffset(fieldIdx);
                        offset = static_cast<unsigned>(offsetInBits / 8);
                        llvm::outs() << "[ConstructorHandler] C2: Non-virtual base " << baseRecord->getNameAsString()
                                     << " field '" << firstFieldName << "' found at offset " << offset << " bytes\n";
                        break;
                    }
                    fieldIdx++;
                }
            }
        }

        clang::CallExpr* call = createBaseConstructorCallVariant(
            baseRecord, thisParam, offset, variantSuffix, cASTContext, targetLoc, targetPath, disp, vttParam
        );

        if (call) {
            bodyStmts.push_back(call);
            llvm::outs() << "[ConstructorHandler] C2: Call base constructor for "
                         << baseRecord->getNameAsString() << " with variant " << variantSuffix << " at offset " << offset << "\n";
        }

        baseIndex++;
    }

    // Add member initialization (use base-subobject layout struct already found)
    auto memberInitStmts = translateMemberInitializers(
        ctor, thisParam, cRecordDecl, disp, cppASTContext, cASTContext, targetLoc
    );
    bodyStmts.insert(bodyStmts.end(), memberInitStmts.begin(), memberInitStmts.end());

    // Add lpVtbl initialization
    if (record->isPolymorphic()) {
        auto lpVtblInitStmts = injectLpVtblInit(record, thisParam, cppASTContext, cASTContext, targetLoc);
        bodyStmts.insert(bodyStmts.end(), lpVtblInitStmts.begin(), lpVtblInitStmts.end());
    }

    // Create CompoundStmt
    clang::CompoundStmt* body = clang::CompoundStmt::Create(
        cASTContext,
        bodyStmts,
        clang::FPOptionsOverride(),
        targetLoc,
        targetLoc
    );

    // Set the body on the function declaration
    c2Func->setBody(body);

    llvm::outs() << "[ConstructorHandler] Generated C2 constructor: " << c2Name << "\n";
}

} // namespace cpptoc
