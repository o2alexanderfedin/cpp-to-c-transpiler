/**
 * @file IfStmtHandler.cpp
 * @brief Implementation of IfStmtHandler
 */

#include "dispatch/IfStmtHandler.h"
#include "SourceLocationMapper.h"
#include "mapping/StmtMapper.h"
#include "clang/AST/Stmt.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void IfStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&IfStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&IfStmtHandler::handleIfStmt)
    );
}

bool IfStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");
    return S->getStmtClass() == clang::Stmt::IfStmtClass;
}

void IfStmtHandler::handleIfStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(S->getStmtClass() == clang::Stmt::IfStmtClass && "Must be IfStmt");

    const auto* cppIfStmt = llvm::cast<clang::IfStmt>(S);

    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

    // Check if already processed
    if (stmtMapper.hasCreated(S)) {
        llvm::outs() << "[IfStmtHandler] IfStmt already translated, skipping\n";
        return;
    }

    llvm::outs() << "[IfStmtHandler] Processing IfStmt\n";

    // Dispatch condition expression
    const clang::Expr* cppCond = cppIfStmt->getCond();
    llvm::outs() << "[IfStmtHandler] Dispatching condition\n";
    bool condHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));

    if (!condHandled) {
        llvm::errs() << "[IfStmtHandler] ERROR: Condition not handled\n";
        assert(false && "Condition must be handled");
    }

    clang::Expr* cCond = disp.getExprMapper().getCreated(cppCond);
    assert(cCond && "Condition must be in ExprMapper");

    // Dispatch then branch
    const clang::Stmt* cppThen = cppIfStmt->getThen();
    llvm::outs() << "[IfStmtHandler] Dispatching then branch\n";
    bool thenHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppThen));

    if (!thenHandled) {
        llvm::errs() << "[IfStmtHandler] ERROR: Then branch not handled\n";
        assert(false && "Then branch must be handled");
    }

    clang::Stmt* cThen = stmtMapper.getCreated(cppThen);
    assert(cThen && "Then branch must be in StmtMapper");

    // Dispatch else branch if present
    clang::Stmt* cElse = nullptr;
    if (const clang::Stmt* cppElse = cppIfStmt->getElse()) {
        llvm::outs() << "[IfStmtHandler] Dispatching else branch\n";
        bool elseHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppElse));

        if (!elseHandled) {
            llvm::errs() << "[IfStmtHandler] ERROR: Else branch not handled\n";
            assert(false && "Else branch must be handled");
        }

        cElse = stmtMapper.getCreated(cppElse);
        assert(cElse && "Else branch must be in StmtMapper");
    }

    // Get source location from SourceLocationMapper
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, S);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Create C IfStmt
    clang::IfStmt* cIfStmt = clang::IfStmt::Create(
        cASTContext,
        targetLoc, // if loc
        clang::IfStatementKind::Ordinary,
        nullptr, // init
        nullptr, // condition variable
        cCond,
        targetLoc, // lparen loc
        targetLoc, // rparen loc
        cThen,
        targetLoc, // else loc
        cElse
    );

    llvm::outs() << "[IfStmtHandler] Created C IfStmt\n";

    // Store in StmtMapper
    stmtMapper.setCreated(S, cIfStmt);
}

} // namespace cpptoc
