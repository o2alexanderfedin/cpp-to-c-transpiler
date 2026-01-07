/**
 * @file WhileStmtHandler.cpp
 * @brief Implementation of WhileStmtHandler
 */

#include "dispatch/WhileStmtHandler.h"
#include "mapping/StmtMapper.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Stmt.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void WhileStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&WhileStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&WhileStmtHandler::handleWhileStmt)
    );
}

bool WhileStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");
    return S->getStmtClass() == clang::Stmt::WhileStmtClass;
}

void WhileStmtHandler::handleWhileStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Must be WhileStmt");

    const auto* cppWhile = llvm::cast<clang::WhileStmt>(S);
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (stmtMapper.hasCreated(S)) {
        llvm::outs() << "[WhileStmtHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[WhileStmtHandler] Processing WhileStmt\n";

    // Process condition
    clang::Expr* cCond = nullptr;
    if (const clang::Expr* cppCond = cppWhile->getCond()) {
        llvm::outs() << "[WhileStmtHandler] Dispatching condition expression\n";
        bool condHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));

        if (!condHandled) {
            llvm::errs() << "[WhileStmtHandler] ERROR: Condition not handled\n";
            llvm::errs() << "  Condition type: " << cppCond->getStmtClassName() << "\n";
            assert(false && "Condition must be handled");
        }

        cCond = exprMapper.getCreated(cppCond);
        assert(cCond && "Condition must be in ExprMapper");
    }

    // Process body
    clang::Stmt* cBody = nullptr;
    if (const clang::Stmt* cppBody = cppWhile->getBody()) {
        llvm::outs() << "[WhileStmtHandler] Dispatching body statement\n";
        bool bodyHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));

        if (!bodyHandled) {
            llvm::errs() << "[WhileStmtHandler] ERROR: Body not handled\n";
            llvm::errs() << "  Body type: " << cppBody->getStmtClassName() << "\n";
            assert(false && "Body must be handled");
        }

        cBody = stmtMapper.getCreated(cppBody);
        assert(cBody && "Body must be in StmtMapper");
    }

    // Get source location from target context
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, nullptr);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Create C WhileStmt
    clang::WhileStmt* cWhile = clang::WhileStmt::Create(
        cASTContext,
        nullptr,  // ConditionVariable (C doesn't support this)
        cCond,
        cBody,
        targetLoc,  // WhileLoc
        targetLoc,  // LParenLoc
        targetLoc   // RParenLoc
    );

    llvm::outs() << "[WhileStmtHandler] Created C WhileStmt\n";

    // Store mapping
    stmtMapper.setCreated(S, cWhile);
}

} // namespace cpptoc
