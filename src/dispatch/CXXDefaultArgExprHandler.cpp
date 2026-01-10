/**
 * @file CXXDefaultArgExprHandler.cpp
 * @brief Implementation of CXXDefaultArgExprHandler
 */

#include "dispatch/CXXDefaultArgExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXDefaultArgExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXDefaultArgExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXDefaultArgExprHandler::handleCXXDefaultArgExpr)
    );
}

bool CXXDefaultArgExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXDefaultArgExprClass;
}

void CXXDefaultArgExprHandler::handleCXXDefaultArgExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXDefaultArgExpr");

    const auto* cppDefaultArg = llvm::cast<clang::CXXDefaultArgExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXDefaultArgExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXDefaultArgExprHandler] Processing CXXDefaultArgExpr\n";

    // Get the actual default value expression
    const clang::Expr* defaultExpr = cppDefaultArg->getExpr();

    if (!defaultExpr) {
        llvm::errs() << "[CXXDefaultArgExprHandler] ERROR: No default expression found\n";
        assert(false && "CXXDefaultArgExpr must have a default expression");
    }

    llvm::outs() << "[CXXDefaultArgExprHandler] Dispatching default value expression\n";

    // Dispatch on the actual default value expression
    bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(defaultExpr));

    if (!handled) {
        llvm::errs() << "[CXXDefaultArgExprHandler] ERROR: Default expression not handled\n";
        llvm::errs() << "  Expression type: " << defaultExpr->getStmtClassName() << "\n";
        assert(false && "Default expression must be handled");
    }

    clang::Expr* cDefaultExpr = exprMapper.getCreated(defaultExpr);
    assert(cDefaultExpr && "Default expression must be in ExprMapper");

    llvm::outs() << "[CXXDefaultArgExprHandler] Using translated default expression\n";

    // Store the translated default expression directly
    // (CXXDefaultArgExpr is just a wrapper - we use the underlying expression in C)
    exprMapper.setCreated(E, cDefaultExpr);
}

} // namespace cpptoc
