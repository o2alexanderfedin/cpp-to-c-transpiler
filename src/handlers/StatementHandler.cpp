/**
 * @file StatementHandler.cpp
 * @brief Implementation of StatementHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 *
 * Translation Strategy:
 * - Most statements translate directly (same syntax in C and C++)
 * - Key work is recursively translating sub-statements and expressions
 * - Delegate to ExpressionHandler for expressions
 * - Delegate to VariableHandler for declarations
 */

#include "handlers/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool StatementHandler::canHandle(const clang::Stmt* S) const {
    if (!S) return false;

    // Handle return and compound statements (Phase 1)
    switch (S->getStmtClass()) {
        case clang::Stmt::ReturnStmtClass:
        case clang::Stmt::CompoundStmtClass:
            return true;
        default:
            return false;
    }
}

clang::Stmt* StatementHandler::handleStmt(const clang::Stmt* S, HandlerContext& ctx) {
    if (!S) return nullptr;

    switch (S->getStmtClass()) {
        case clang::Stmt::ReturnStmtClass:
            return translateReturnStmt(llvm::cast<clang::ReturnStmt>(S), ctx);

        case clang::Stmt::CompoundStmtClass:
            return translateCompoundStmt(llvm::cast<clang::CompoundStmt>(S), ctx);

        default:
            // For now, pass through other statements
            // TODO: Add support for more statement types in later phases
            return const_cast<clang::Stmt*>(S);
    }
}

clang::ReturnStmt* StatementHandler::translateReturnStmt(
    const clang::ReturnStmt* RS,
    HandlerContext& ctx
) {
    // Get return expression (may be null for void return)
    const clang::Expr* retValue = RS->getRetValue();
    clang::Expr* cRetValue = nullptr;

    if (retValue) {
        // For now, pass through the expression
        // TODO: Delegate to ExpressionHandler when available
        cRetValue = const_cast<clang::Expr*>(retValue);
    }

    // Create C return statement using CNodeBuilder
    clang::ASTContext& cContext = ctx.getCContext();
    return clang::ReturnStmt::Create(
        cContext,
        RS->getReturnLoc(),
        cRetValue,
        nullptr // NRVOCandidate
    );
}

clang::CompoundStmt* StatementHandler::translateCompoundStmt(
    const clang::CompoundStmt* CS,
    HandlerContext& ctx
) {
    // Translate each statement in the compound statement
    std::vector<clang::Stmt*> cStmts;

    for (const clang::Stmt* S : CS->body()) {
        clang::Stmt* cStmt = handleStmt(S, ctx);
        if (cStmt) {
            cStmts.push_back(cStmt);
        }
    }

    // Create C compound statement using CNodeBuilder
    clang::ASTContext& cContext = ctx.getCContext();
    return clang::CompoundStmt::Create(
        cContext,
        cStmts,
        clang::FPOptionsOverride(),
        CS->getLBracLoc(),
        CS->getRBracLoc()
    );
}

} // namespace cpptoc
