/**
 * @file BinaryOperatorHandler.cpp
 * @brief Implementation of BinaryOperatorHandler with recursive dispatch
 */

#include "dispatch/BinaryOperatorHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void BinaryOperatorHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&BinaryOperatorHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&BinaryOperatorHandler::handleBinaryOperator)
    );
}

bool BinaryOperatorHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::BinaryOperatorClass;
}

void BinaryOperatorHandler::handleBinaryOperator(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::BinaryOperatorClass && "Must be BinaryOperator");

    const auto* cppBinOp = llvm::cast<clang::BinaryOperator>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreatedExpr(E)) {
        llvm::outs() << "[BinaryOperatorHandler] BinaryOperator already translated, skipping\n";
        return;
    }

    // Extract LHS and RHS subexpressions
    const clang::Expr* cppLHS = cppBinOp->getLHS();
    const clang::Expr* cppRHS = cppBinOp->getRHS();

    llvm::outs() << "[BinaryOperatorHandler] Processing BinaryOperator: "
                 << cppBinOp->getOpcodeStr().str() << "\n";

    // CRITICAL: Recursive dispatch pattern
    // Dispatch LHS via dispatcher (may trigger LiteralHandler, DeclRefExprHandler, BinaryOperatorHandler, etc.)
    llvm::outs() << "[BinaryOperatorHandler] Dispatching LHS subexpression\n";
    bool lhsHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppLHS));

    if (!lhsHandled) {
        llvm::errs() << "[BinaryOperatorHandler] ERROR: LHS not handled by any expression handler\n";
        assert(false && "LHS must be handled");
    }

    // Retrieve translated LHS from ExprMapper
    clang::Expr* cLHS = exprMapper.getCreatedExpr(cppLHS);
    assert(cLHS && "LHS must be in ExprMapper after dispatch");

    // Dispatch RHS via dispatcher (recursive)
    llvm::outs() << "[BinaryOperatorHandler] Dispatching RHS subexpression\n";
    bool rhsHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppRHS));

    if (!rhsHandled) {
        llvm::errs() << "[BinaryOperatorHandler] ERROR: RHS not handled by any expression handler\n";
        assert(false && "RHS must be handled");
    }

    // Retrieve translated RHS from ExprMapper
    clang::Expr* cRHS = exprMapper.getCreatedExpr(cppRHS);
    assert(cRHS && "RHS must be in ExprMapper after dispatch");

    llvm::outs() << "[BinaryOperatorHandler] Both operands translated successfully\n";

    // Create C BinaryOperator with translated operands
    clang::BinaryOperator* cBinOp = clang::BinaryOperator::Create(
        cASTContext,
        cLHS,
        cRHS,
        cppBinOp->getOpcode(),
        cppBinOp->getType(),  // May need type translation in future
        cppBinOp->getValueKind(),
        cppBinOp->getObjectKind(),
        clang::SourceLocation(),
        clang::FPOptionsOverride()
    );

    llvm::outs() << "[BinaryOperatorHandler] Created C BinaryOperator: "
                 << cppBinOp->getOpcodeStr().str() << "\n";

    // Store mapping in ExprMapper
    exprMapper.setCreatedExpr(E, cBinOp);
}

} // namespace cpptoc
