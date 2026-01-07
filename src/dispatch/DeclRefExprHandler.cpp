/**
 * @file DeclRefExprHandler.cpp
 * @brief Implementation of DeclRefExprHandler dispatcher pattern
 */

#include "dispatch/DeclRefExprHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "SourceLocationMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Decl.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void DeclRefExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&DeclRefExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&DeclRefExprHandler::handleDeclRefExpr)
    );
}

bool DeclRefExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::DeclRefExprClass;
}

void DeclRefExprHandler::handleDeclRefExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::DeclRefExprClass && "Must be DeclRefExpr");

    const auto* cppDeclRef = llvm::cast<clang::DeclRefExpr>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[DeclRefExprHandler] DeclRefExpr already translated, skipping\n";
        return;
    }

    // Get the referenced declaration
    const clang::ValueDecl* cppDecl = cppDeclRef->getDecl();

    // Try to retrieve C declaration from DeclMapper
    // (It should have been created by ParameterHandler, VarDeclHandler, etc.)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    clang::Decl* cDecl = declMapper.getCreated(cppDecl);

    // If C declaration doesn't exist yet, this is a forward reference issue
    // For Phase 1, we'll use the C++ declaration as fallback
    // TODO: Implement proper declaration ordering to ensure declarations exist
    if (!cDecl) {
        llvm::outs() << "[DeclRefExprHandler] WARNING: Referenced declaration not found in DeclMapper: "
                     << cppDecl->getNameAsString() << "\n";
        llvm::outs() << "[DeclRefExprHandler] Using C++ declaration as fallback (will need proper translation)\n";
        cDecl = const_cast<clang::ValueDecl*>(cppDecl);
    }

    // Cast to ValueDecl (required for DeclRefExpr)
    clang::ValueDecl* cValueDecl = llvm::dyn_cast<clang::ValueDecl>(cDecl);
    assert(cValueDecl && "Declaration must be ValueDecl for DeclRefExpr");

    // Check if original C++ declaration was a reference type
    // If so, we need to wrap the DeclRefExpr with a dereference operator
    bool needsDereference = false;
    clang::QualType resultType = cppDeclRef->getType();

    // Check if this is a parameter with reference type
    if (const auto* cppParmVar = llvm::dyn_cast<clang::ParmVarDecl>(cppDecl)) {
        clang::QualType cppParamType = cppParmVar->getType();
        if (cppParamType->isLValueReferenceType() || cppParamType->isRValueReferenceType()) {
            needsDereference = true;
            // The result type should be the pointee type (without reference)
            resultType = cppParamType.getNonReferenceType();
        }
    }

    // Get valid SourceLocation for C AST nodes
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, cppDecl);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Create C DeclRefExpr
    clang::DeclRefExpr* cDeclRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),  // No nested name specifier in C
        targetLoc,                        // Template keyword location (from target path)
        cValueDecl,
        false,                            // refersToEnclosingVariableOrCapture
        targetLoc,                        // Location (from target path)
        needsDereference ? cASTContext.getPointerType(resultType) : resultType,
        clang::VK_LValue                  // Value kind
    );

    clang::Expr* resultExpr = cDeclRef;

    // If this was a reference parameter, wrap with dereference operator
    if (needsDereference) {
        llvm::outs() << "[DeclRefExprHandler] Parameter was reference type, wrapping with dereference: "
                     << cppDecl->getNameAsString() << "\n";

        resultExpr = clang::UnaryOperator::Create(
            cASTContext,
            cDeclRef,
            clang::UO_Deref,
            resultType,
            clang::VK_LValue,
            clang::OK_Ordinary,
            targetLoc,  // Location from target path
            false,  // canOverflow
            clang::FPOptionsOverride()
        );
    }

    llvm::outs() << "[DeclRefExprHandler] Translated DeclRefExpr: "
                 << cppDecl->getNameAsString() << "\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, resultExpr);
}

} // namespace cpptoc
