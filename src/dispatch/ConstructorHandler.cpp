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

    // Phase 3: Generate C1/C2 constructors for classes with virtual inheritance
    if (needsConstructorVariants(ctor)) {
        llvm::outs() << "[ConstructorHandler] Class " << className
                     << " needs C1/C2 constructor variants\n";

        // Generate C1 (complete-object) constructor
        generateC1Constructor(ctor, cppASTContext, cASTContext, disp);

        // Generate C2 (base-subobject) constructor
        generateC2Constructor(ctor, cppASTContext, cASTContext, disp);
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

    unsigned baseIndex = 0;
    for (const auto& base : parentClass->bases()) {
        const auto* baseClass = base.getType()->getAsCXXRecordDecl();
        if (!baseClass) continue;

        unsigned offset = 0;
        if (baseIndex > 0 && parentClass->isCompleteDefinition()) {
            const clang::ASTRecordLayout& layout = cppASTContext.getASTRecordLayout(parentClass);
            clang::CharUnits baseOffset = layout.getBaseClassOffset(baseClass);
            offset = static_cast<unsigned>(baseOffset.getQuantity());
        }

        clang::CallExpr* call = createBaseConstructorCall(baseClass, thisParam, offset, cASTContext, targetLoc);
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

// Phase 3: Constructor Variant Generation

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

    if (viAnalyzer.needsVTT(record)) {
        clang::IdentifierInfo& vttII = cASTContext.Idents.get("vtt");
        clang::QualType voidPtrType = cASTContext.getPointerType(cASTContext.VoidTy);
        clang::QualType constVoidPtrType = cASTContext.getConstType(voidPtrType);
        clang::QualType vttType = cASTContext.getPointerType(constVoidPtrType);

        clang::ParmVarDecl* vttParam = clang::ParmVarDecl::Create(
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

    // Build constructor body
    std::vector<clang::Stmt*> bodyStmts;

    // C1: Initialize virtual bases FIRST (C1 responsibility)
    auto virtualBases = viAnalyzer.getVirtualBases(record);
    for (const auto* vbase : virtualBases) {
        // TODO: Generate virtual base constructor calls
        // For now, add a comment placeholder
        llvm::outs() << "[ConstructorHandler] C1: TODO: Initialize virtual base "
                     << vbase->getNameAsString() << "\n";
    }

    // Call non-virtual base constructors (use C2 variants if they have virtual bases)
    for (const auto& base : record->bases()) {
        if (base.isVirtual()) continue; // Skip virtual bases (already handled)

        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        // TODO: Generate base constructor call (C2 if base needs variants, C1 otherwise)
        llvm::outs() << "[ConstructorHandler] C1: TODO: Call base constructor for "
                     << baseRecord->getNameAsString() << "\n";
    }

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

    // Create C function
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* c1Func = builder.funcDecl(
        c1Name,
        cASTContext.VoidTy,
        allParams,
        body
    );

    assert(c1Func && "Failed to create C1 FunctionDecl");

    // Register mapping (create unique key for C1 variant)
    // Note: We can't use the same key as the original constructor
    // For now, just add to TU without mapping
    c1Func->setDeclContext(TU);
    TU->addDecl(c1Func);
    pathMapper.setNodeLocation(c1Func, targetPath);

    llvm::outs() << "[ConstructorHandler] Generated C1 constructor: " << c1Name << "\n";
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

    if (viAnalyzer.needsVTT(record)) {
        clang::IdentifierInfo& vttII = cASTContext.Idents.get("vtt");
        clang::QualType voidPtrType = cASTContext.getPointerType(cASTContext.VoidTy);
        clang::QualType constVoidPtrType = cASTContext.getConstType(voidPtrType);
        clang::QualType vttType = cASTContext.getPointerType(constVoidPtrType);

        clang::ParmVarDecl* vttParam = clang::ParmVarDecl::Create(
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

    // Build constructor body
    std::vector<clang::Stmt*> bodyStmts;

    // C2: SKIP virtual base initialization (parent's C1 handles it)

    // Call non-virtual base constructors (use C2 variants if they have virtual bases)
    for (const auto& base : record->bases()) {
        if (base.isVirtual()) continue; // Skip virtual bases

        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        // TODO: Generate base constructor call (C2 if base needs variants, C1 otherwise)
        llvm::outs() << "[ConstructorHandler] C2: TODO: Call base constructor for "
                     << baseRecord->getNameAsString() << "\n";
    }

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

    // Create C function
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* c2Func = builder.funcDecl(
        c2Name,
        cASTContext.VoidTy,
        allParams,
        body
    );

    assert(c2Func && "Failed to create C2 FunctionDecl");

    // Register mapping (create unique key for C2 variant)
    // Note: We can't use the same key as the original constructor
    // For now, just add to TU without mapping
    c2Func->setDeclContext(TU);
    TU->addDecl(c2Func);
    pathMapper.setNodeLocation(c2Func, targetPath);

    llvm::outs() << "[ConstructorHandler] Generated C2 constructor: " << c2Name << "\n";
}

} // namespace cpptoc
