/**
 * @file ExprWithCleanupsHandler.cpp
 * @brief Implementation of ExprWithCleanupsHandler dispatcher pattern
 */

#include "dispatch/ExprWithCleanupsHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ExprWithCleanupsHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to ExprPredicate and ExprVisitor to avoid ambiguity
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&ExprWithCleanupsHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&ExprWithCleanupsHandler::handleExprWithCleanups)
    );
}

bool ExprWithCleanupsHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::ExprWithCleanupsClass;
}

void ExprWithCleanupsHandler::handleExprWithCleanups(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Expression must be ExprWithCleanups");

    const auto* cppCleanups = llvm::cast<clang::ExprWithCleanups>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(cppCleanups)) {
        llvm::outs() << "[ExprWithCleanupsHandler] ExprWithCleanups already translated, skipping\n";
        return;
    }

    llvm::outs() << "[ExprWithCleanupsHandler] Processing ExprWithCleanups\n";
    llvm::outs() << "[ExprWithCleanupsHandler] Note: C doesn't have RAII cleanup, unwrapping to subexpression\n";

    // Extract subexpression (the actual expression without cleanup wrapper)
    const clang::Expr* cppSubExpr = cppCleanups->getSubExpr();
    assert(cppSubExpr && "ExprWithCleanups must have subexpression");

    // CRITICAL: Dispatch subexpression via dispatcher (recursive)
    llvm::outs() << "[ExprWithCleanupsHandler] Dispatching subexpression (type: "
                 << cppSubExpr->getStmtClassName() << ")\n";
    bool subExprHandled = disp.dispatch(
        cppASTContext,
        cASTContext,
        const_cast<clang::Expr*>(cppSubExpr)
    );

    // Retrieve translated subexpression from ExprMapper
    clang::Expr* cSubExpr = exprMapper.getCreated(cppSubExpr);

    if (!cSubExpr) {
        llvm::errs() << "[ExprWithCleanupsHandler] ERROR: Failed to retrieve translated subexpression\n";
        llvm::errs() << "  Subexpression type: " << cppSubExpr->getStmtClassName() << "\n";
        llvm::errs() << "  Was handled: " << (subExprHandled ? "yes" : "no") << "\n";
        assert(false && "ExprWithCleanups subexpression must be translated");
    }

    llvm::outs() << "[ExprWithCleanupsHandler] Subexpression translated successfully\n";

    // CRITICAL: Map ExprWithCleanups directly to translated subexpression
    // This unwraps the cleanup wrapper since C doesn't support RAII
    // The outer ExprWithCleanups node transparently passes through to the inner expression
    llvm::outs() << "[ExprWithCleanupsHandler] Mapping ExprWithCleanups directly to subexpression (transparent unwrap)\n";
    exprMapper.setCreated(cppCleanups, cSubExpr);

    llvm::outs() << "[ExprWithCleanupsHandler] ExprWithCleanups successfully unwrapped\n";
}

} // namespace cpptoc
