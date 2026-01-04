/**
 * @file ExprWithCleanupsHandler.cpp
 * @brief Implementation of ExprWithCleanupsHandler
 */

#include "dispatch/ExprWithCleanupsHandler.h"
#include "mapping/StmtMapper.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ExprWithCleanupsHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&ExprWithCleanupsHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&ExprWithCleanupsHandler::handleExprWithCleanups)
    );
}

bool ExprWithCleanupsHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");
    return S->getStmtClass() == clang::Stmt::ExprWithCleanupsClass;
}

void ExprWithCleanupsHandler::handleExprWithCleanups(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Must be ExprWithCleanups");

    const auto* cppCleanups = llvm::cast<clang::ExprWithCleanups>(S);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

    // Check if already processed
    if (exprMapper.hasCreated(llvm::cast<clang::Expr>(S))) {
        llvm::outs() << "[ExprWithCleanupsHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[ExprWithCleanupsHandler] Processing ExprWithCleanups\n";
    llvm::outs() << "[ExprWithCleanupsHandler] Note: C doesn't have RAII cleanup, using subexpression directly\n";

    // Get the subexpression (the actual expression without cleanup)
    const clang::Expr* cppSubExpr = cppCleanups->getSubExpr();

    // Dispatch subexpression
    bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppSubExpr));

    if (!handled) {
        llvm::errs() << "[ExprWithCleanupsHandler] ERROR: Subexpression not handled\n";
        llvm::errs() << "  Subexpression type: " << cppSubExpr->getStmtClassName() << "\n";
        assert(false && "Subexpression must be handled");
    }

    clang::Expr* cSubExpr = exprMapper.getCreated(cppSubExpr);
    assert(cSubExpr && "Subexpression must be in ExprMapper");

    llvm::outs() << "[ExprWithCleanupsHandler] Using subexpression directly (cleanup actions omitted in C)\n";

    // Store the subexpression directly (ExprWithCleanups is just a wrapper)
    exprMapper.setCreated(llvm::cast<clang::Expr>(S), cSubExpr);
    stmtMapper.setCreated(S, cSubExpr);
}

} // namespace cpptoc
