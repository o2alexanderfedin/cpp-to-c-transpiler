/**
 * @file UnaryOperatorHandler.cpp
 * @brief Implementation of UnaryOperatorHandler with recursive dispatch
 */

#include "dispatch/UnaryOperatorHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void UnaryOperatorHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&UnaryOperatorHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&UnaryOperatorHandler::handleUnaryOperator)
    );
}

bool UnaryOperatorHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::UnaryOperatorClass;
}

void UnaryOperatorHandler::handleUnaryOperator(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::UnaryOperatorClass && "Must be UnaryOperator");

    const auto* cppUnOp = llvm::cast<clang::UnaryOperator>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreatedExpr(E)) {
        llvm::outs() << "[UnaryOperatorHandler] UnaryOperator already translated, skipping\n";
        return;
    }

    // Extract operand subexpression
    const clang::Expr* cppOperand = cppUnOp->getSubExpr();

    llvm::outs() << "[UnaryOperatorHandler] Processing UnaryOperator: "
                 << clang::UnaryOperator::getOpcodeStr(cppUnOp->getOpcode()).str() << "\n";

    // CRITICAL: Recursive dispatch pattern
    // Dispatch operand via dispatcher (may trigger LiteralHandler, DeclRefExprHandler, etc.)
    llvm::outs() << "[UnaryOperatorHandler] Dispatching operand subexpression\n";
    bool operandHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppOperand));

    if (!operandHandled) {
        llvm::errs() << "[UnaryOperatorHandler] ERROR: Operand not handled by any expression handler\n";
        assert(false && "Operand must be handled");
    }

    // Retrieve translated operand from ExprMapper
    clang::Expr* cOperand = exprMapper.getCreatedExpr(cppOperand);
    assert(cOperand && "Operand must be in ExprMapper after dispatch");

    llvm::outs() << "[UnaryOperatorHandler] Operand translated successfully\n";

    // Create C UnaryOperator with translated operand
    clang::UnaryOperator* cUnOp = clang::UnaryOperator::Create(
        cASTContext,
        cOperand,
        cppUnOp->getOpcode(),
        cppUnOp->getType(),  // May need type translation in future
        cppUnOp->getValueKind(),
        cppUnOp->getObjectKind(),
        clang::SourceLocation(),
        cppUnOp->canOverflow(),
        clang::FPOptionsOverride()
    );

    llvm::outs() << "[UnaryOperatorHandler] Created C UnaryOperator: "
                 << clang::UnaryOperator::getOpcodeStr(cppUnOp->getOpcode()).str() << "\n";

    // Store mapping in ExprMapper
    exprMapper.setCreatedExpr(E, cUnOp);
}

} // namespace cpptoc
