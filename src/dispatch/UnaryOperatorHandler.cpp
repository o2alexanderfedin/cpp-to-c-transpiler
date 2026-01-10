/**
 * @file UnaryOperatorHandler.cpp
 * @brief Implementation of UnaryOperatorHandler with recursive dispatch
 */

#include "dispatch/UnaryOperatorHandler.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "TargetContext.h"
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
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[UnaryOperatorHandler] UnaryOperator already translated, skipping\n";
        return;
    }

    // Get target location for this expression
    std::string targetPath = disp.getCurrentTargetPath();
    assert(!targetPath.empty() && "Target path must be set before expression handling");
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

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
    clang::Expr* cOperand = exprMapper.getCreated(cppOperand);
    assert(cOperand && "Operand must be in ExprMapper after dispatch");

    llvm::outs() << "[UnaryOperatorHandler] Operand translated successfully\n";

    // Create C UnaryOperator with translated operand
    clang::UnaryOperator* cUnOp = clang::UnaryOperator::Create(
        cASTContext,
        cOperand,
        cppUnOp->getOpcode(),
        cppUnOp->getType(),
        cppUnOp->getValueKind(),
        cppUnOp->getObjectKind(),
        targetLoc,
        cppUnOp->canOverflow(),
        clang::FPOptionsOverride()
    );

    llvm::outs() << "[UnaryOperatorHandler] Created C UnaryOperator: "
                 << clang::UnaryOperator::getOpcodeStr(cppUnOp->getOpcode()).str() << "\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, cUnOp);
}

} // namespace cpptoc
