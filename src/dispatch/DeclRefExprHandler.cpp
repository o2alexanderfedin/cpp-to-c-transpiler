/**
 * @file DeclRefExprHandler.cpp
 * @brief Implementation of DeclRefExprHandler dispatcher pattern
 */

#include "dispatch/DeclRefExprHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
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

    // Create C DeclRefExpr
    clang::DeclRefExpr* cDeclRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),  // No nested name specifier in C
        clang::SourceLocation(),          // No template keyword location
        cValueDecl,
        false,                            // refersToEnclosingVariableOrCapture
        clang::SourceLocation(),          // Location
        cppDeclRef->getType(),            // Type (may need translation in future)
        clang::VK_LValue                  // Value kind
    );

    llvm::outs() << "[DeclRefExprHandler] Translated DeclRefExpr: "
                 << cppDecl->getNameAsString() << "\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, cDeclRef);
}

} // namespace cpptoc
