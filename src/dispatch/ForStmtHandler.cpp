/**
 * @file ForStmtHandler.cpp
 * @brief Implementation of ForStmtHandler
 */

#include "dispatch/ForStmtHandler.h"
#include "mapping/StmtMapper.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Stmt.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ForStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&ForStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&ForStmtHandler::handleForStmt)
    );
}

bool ForStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");
    return S->getStmtClass() == clang::Stmt::ForStmtClass;
}

void ForStmtHandler::handleForStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Must be ForStmt");

    const auto* cppFor = llvm::cast<clang::ForStmt>(S);
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (stmtMapper.hasCreated(S)) {
        llvm::outs() << "[ForStmtHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[ForStmtHandler] Processing ForStmt\n";

    // Process Init statement (can be DeclStmt or Expr)
    clang::Stmt* cInit = nullptr;
    if (const clang::Stmt* cppInit = cppFor->getInit()) {
        llvm::outs() << "[ForStmtHandler] Dispatching init statement\n";
        bool initHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppInit));

        if (!initHandled) {
            llvm::errs() << "[ForStmtHandler] ERROR: Init statement not handled\n";
            llvm::errs() << "  Init statement type: " << cppInit->getStmtClassName() << "\n";
            assert(false && "Init statement must be handled");
        }

        cInit = stmtMapper.getCreated(cppInit);
        assert(cInit && "Init statement must be in StmtMapper");
    }

    // Process Cond expression
    clang::Expr* cCond = nullptr;
    if (const clang::Expr* cppCond = cppFor->getCond()) {
        llvm::outs() << "[ForStmtHandler] Dispatching condition expression\n";
        bool condHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));

        if (!condHandled) {
            llvm::errs() << "[ForStmtHandler] ERROR: Condition expression not handled\n";
            llvm::errs() << "  Condition expression type: " << cppCond->getStmtClassName() << "\n";
            assert(false && "Condition expression must be handled");
        }

        cCond = exprMapper.getCreated(cppCond);
        assert(cCond && "Condition expression must be in ExprMapper");
    }

    // Process Inc expression
    clang::Expr* cInc = nullptr;
    if (const clang::Expr* cppInc = cppFor->getInc()) {
        llvm::outs() << "[ForStmtHandler] Dispatching increment expression\n";
        bool incHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppInc));

        if (!incHandled) {
            llvm::errs() << "[ForStmtHandler] ERROR: Increment expression not handled\n";
            llvm::errs() << "  Increment expression type: " << cppInc->getStmtClassName() << "\n";
            assert(false && "Increment expression must be handled");
        }

        cInc = exprMapper.getCreated(cppInc);
        assert(cInc && "Increment expression must be in ExprMapper");
    }

    // Process Body statement
    clang::Stmt* cBody = nullptr;
    if (const clang::Stmt* cppBody = cppFor->getBody()) {
        llvm::outs() << "[ForStmtHandler] Dispatching body statement\n";
        bool bodyHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));

        if (!bodyHandled) {
            llvm::errs() << "[ForStmtHandler] ERROR: Body statement not handled\n";
            llvm::errs() << "  Body statement type: " << cppBody->getStmtClassName() << "\n";
            assert(false && "Body statement must be handled");
        }

        cBody = stmtMapper.getCreated(cppBody);
        assert(cBody && "Body statement must be in StmtMapper");
    }

    // Get valid SourceLocation for C AST nodes
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, nullptr);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Create C ForStmt
    clang::ForStmt* cFor = new (cASTContext) clang::ForStmt(
        cASTContext,
        cInit,
        cCond,
        nullptr,  // ConditionVariable (not used in C)
        cInc,
        cBody,
        targetLoc,  // ForLoc (from target path)
        targetLoc,  // LParenLoc (from target path)
        targetLoc   // RParenLoc (from target path)
    );

    llvm::outs() << "[ForStmtHandler] Created C ForStmt\n";

    // Store mapping
    stmtMapper.setCreated(S, cFor);
}

} // namespace cpptoc
