/**
 * @file ConditionalOperatorHandler.cpp
 * @brief Implementation of ConditionalOperatorHandler
 */

#include "dispatch/ConditionalOperatorHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ConditionalOperatorHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&ConditionalOperatorHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&ConditionalOperatorHandler::handleConditionalOperator)
    );
}

bool ConditionalOperatorHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::ConditionalOperatorClass;
}

void ConditionalOperatorHandler::handleConditionalOperator(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be ConditionalOperator");

    const auto* cppCond = llvm::cast<clang::ConditionalOperator>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[ConditionalOperatorHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[ConditionalOperatorHandler] Processing ConditionalOperator (? :)\n";

    // Dispatch condition expression
    const clang::Expr* cppCondExpr = cppCond->getCond();
    bool condHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCondExpr));

    if (!condHandled) {
        llvm::errs() << "[ConditionalOperatorHandler] ERROR: Condition not handled\n";
        llvm::errs() << "  Condition expression type: " << cppCondExpr->getStmtClassName() << "\n";
        assert(false && "Condition must be handled");
    }

    clang::Expr* cCondExpr = exprMapper.getCreated(cppCondExpr);
    assert(cCondExpr && "Condition must be in ExprMapper");

    // Dispatch true expression
    const clang::Expr* cppTrueExpr = cppCond->getTrueExpr();
    bool trueHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppTrueExpr));

    if (!trueHandled) {
        llvm::errs() << "[ConditionalOperatorHandler] ERROR: True expression not handled\n";
        llvm::errs() << "  True expression type: " << cppTrueExpr->getStmtClassName() << "\n";
        assert(false && "True expression must be handled");
    }

    clang::Expr* cTrueExpr = exprMapper.getCreated(cppTrueExpr);
    assert(cTrueExpr && "True expression must be in ExprMapper");

    // Dispatch false expression
    const clang::Expr* cppFalseExpr = cppCond->getFalseExpr();
    bool falseHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppFalseExpr));

    if (!falseHandled) {
        llvm::errs() << "[ConditionalOperatorHandler] ERROR: False expression not handled\n";
        llvm::errs() << "  False expression type: " << cppFalseExpr->getStmtClassName() << "\n";
        assert(false && "False expression must be handled");
    }

    clang::Expr* cFalseExpr = exprMapper.getCreated(cppFalseExpr);
    assert(cFalseExpr && "False expression must be in ExprMapper");

    // Create C conditional operator
    clang::ConditionalOperator* cCondOp = new (cASTContext) clang::ConditionalOperator(
        cCondExpr,
        clang::SourceLocation(),  // QuestionLoc
        cTrueExpr,
        clang::SourceLocation(),  // ColonLoc
        cFalseExpr,
        cppCond->getType(),
        cppCond->getValueKind(),
        cppCond->getObjectKind()
    );

    llvm::outs() << "[ConditionalOperatorHandler] Created ConditionalOperator\n";

    // Store mapping
    exprMapper.setCreated(E, cCondOp);
}

} // namespace cpptoc
