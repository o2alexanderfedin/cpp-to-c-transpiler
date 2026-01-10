/**
 * @file SwitchStmtHandler.cpp
 * @brief Implementation of SwitchStmtHandler
 */

#include "dispatch/SwitchStmtHandler.h"
#include "mapping/StmtMapper.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Stmt.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void SwitchStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&SwitchStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&SwitchStmtHandler::handleSwitchStmt)
    );
}

bool SwitchStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");
    return S->getStmtClass() == clang::Stmt::SwitchStmtClass;
}

void SwitchStmtHandler::handleSwitchStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Must be SwitchStmt");

    const auto* cppSwitch = llvm::cast<clang::SwitchStmt>(S);
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (stmtMapper.hasCreated(S)) {
        llvm::outs() << "[SwitchStmtHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[SwitchStmtHandler] Processing SwitchStmt\n";

    // Process condition
    clang::Expr* cCond = nullptr;
    if (const clang::Expr* cppCond = cppSwitch->getCond()) {
        llvm::outs() << "[SwitchStmtHandler] Dispatching condition expression\n";
        bool condHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));

        if (!condHandled) {
            llvm::errs() << "[SwitchStmtHandler] ERROR: Condition not handled\n";
            llvm::errs() << "  Condition type: " << cppCond->getStmtClassName() << "\n";
            assert(false && "Condition must be handled");
        }

        cCond = exprMapper.getCreated(cppCond);
        assert(cCond && "Condition must be in ExprMapper");
    }

    // Process body
    clang::Stmt* cBody = nullptr;
    if (const clang::Stmt* cppBody = cppSwitch->getBody()) {
        llvm::outs() << "[SwitchStmtHandler] Dispatching body statement\n";
        bool bodyHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));

        if (!bodyHandled) {
            llvm::errs() << "[SwitchStmtHandler] ERROR: Body not handled\n";
            llvm::errs() << "  Body type: " << cppBody->getStmtClassName() << "\n";
            assert(false && "Body must be handled");
        }

        cBody = stmtMapper.getCreated(cppBody);
        assert(cBody && "Body must be in StmtMapper");
    }

    // Get source location for SourceLocation initialization
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile("");

    // Create C SwitchStmt (body is set separately)
    clang::SwitchStmt* cSwitch = clang::SwitchStmt::Create(
        cASTContext,
        nullptr,  // Init statement (C doesn't support this)
        nullptr,  // ConditionVariable (C doesn't support this)
        cCond,
        targetLoc,  // LParenLoc
        targetLoc   // RParenLoc
    );

    // Set the body separately
    if (cBody) {
        cSwitch->setBody(cBody);
    }

    llvm::outs() << "[SwitchStmtHandler] Created C SwitchStmt\n";

    // Store mapping
    stmtMapper.setCreated(S, cSwitch);
}

} // namespace cpptoc
