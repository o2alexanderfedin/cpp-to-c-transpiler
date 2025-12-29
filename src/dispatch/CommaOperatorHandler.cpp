/**
 * @file CommaOperatorHandler.cpp
 * @brief Implementation of CommaOperatorHandler with recursive dispatch
 */

#include "dispatch/CommaOperatorHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CommaOperatorHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CommaOperatorHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CommaOperatorHandler::handleCommaOperator)
    );
}

bool CommaOperatorHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Check if it's a BinaryOperator with BO_Comma opcode
    if (E->getStmtClass() != clang::Stmt::BinaryOperatorClass) {
        return false;
    }

    const auto* binOp = llvm::cast<clang::BinaryOperator>(E);
    return binOp->getOpcode() == clang::BO_Comma;
}

void CommaOperatorHandler::handleCommaOperator(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::BinaryOperatorClass && "Must be BinaryOperator");

    const auto* cppCommaOp = llvm::cast<clang::BinaryOperator>(E);
    assert(cppCommaOp->getOpcode() == clang::BO_Comma && "Must be BO_Comma");

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CommaOperatorHandler] Comma operator already translated, skipping\n";
        return;
    }

    // Extract LHS and RHS subexpressions
    const clang::Expr* cppLHS = cppCommaOp->getLHS();
    const clang::Expr* cppRHS = cppCommaOp->getRHS();

    llvm::outs() << "[CommaOperatorHandler] Processing comma operator\n";

    // CRITICAL: Recursive dispatch pattern
    // Dispatch LHS via dispatcher (may trigger any expression handler)
    llvm::outs() << "[CommaOperatorHandler] Dispatching LHS subexpression\n";
    bool lhsHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppLHS));

    if (!lhsHandled) {
        llvm::errs() << "[CommaOperatorHandler] ERROR: LHS not handled by any expression handler\n";
        assert(false && "LHS must be handled");
    }

    // Retrieve translated LHS from ExprMapper
    clang::Expr* cLHS = exprMapper.getCreated(cppLHS);
    assert(cLHS && "LHS must be in ExprMapper after dispatch");

    // Dispatch RHS via dispatcher (recursive)
    llvm::outs() << "[CommaOperatorHandler] Dispatching RHS subexpression\n";
    bool rhsHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppRHS));

    if (!rhsHandled) {
        llvm::errs() << "[CommaOperatorHandler] ERROR: RHS not handled by any expression handler\n";
        assert(false && "RHS must be handled");
    }

    // Retrieve translated RHS from ExprMapper
    clang::Expr* cRHS = exprMapper.getCreated(cppRHS);
    assert(cRHS && "RHS must be in ExprMapper after dispatch");

    llvm::outs() << "[CommaOperatorHandler] Both operands translated successfully\n";

    // Create C BinaryOperator with BO_Comma opcode and translated operands
    clang::BinaryOperator* cCommaOp = clang::BinaryOperator::Create(
        cASTContext,
        cLHS,
        cRHS,
        clang::BO_Comma,
        cppCommaOp->getType(),  // May need type translation in future
        cppCommaOp->getValueKind(),
        cppCommaOp->getObjectKind(),
        clang::SourceLocation(),
        clang::FPOptionsOverride()
    );

    llvm::outs() << "[CommaOperatorHandler] Created C comma operator\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, cCommaOp);
}

} // namespace cpptoc
