/**
 * @file ConstantExprHandler.cpp
 * @brief Implementation of ConstantExprHandler dispatcher pattern
 */

#include "dispatch/ConstantExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ConstantExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&ConstantExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&ConstantExprHandler::handleConstantExpr)
    );
}

bool ConstantExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::ConstantExprClass;
}

void ConstantExprHandler::handleConstantExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::ConstantExprClass && "Must be ConstantExpr");

    const auto* cppConstExpr = llvm::cast<clang::ConstantExpr>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[ConstantExprHandler] ConstantExpr already translated, skipping\n";
        return;
    }

    // Get the subexpression (the actual constant value)
    const clang::Expr* subExpr = cppConstExpr->getSubExpr();
    assert(subExpr && "ConstantExpr must have a subexpression");

    // Dispatch subexpression to appropriate handler
    // (typically DeclRefExpr for enum constants, IntegerLiteral for numeric constants)
    bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(subExpr));

    if (!handled) {
        llvm::errs() << "[ConstantExprHandler] ERROR: Subexpression not handled: "
                     << subExpr->getStmtClassName() << "\n";
        assert(false && "ConstantExpr subexpression must be handled");
        return;
    }

    // Retrieve the translated subexpression
    clang::Expr* cSubExpr = exprMapper.getCreated(subExpr);
    assert(cSubExpr && "Subexpression must be in ExprMapper after successful dispatch");

    // In C, we don't have ConstantExpr wrapper, so we just use the subexpression directly
    // Map the C++ ConstantExpr to the C subexpression
    exprMapper.setCreated(E, cSubExpr);

    llvm::outs() << "[ConstantExprHandler] Unwrapped ConstantExpr, using subexpression\n";
}

} // namespace cpptoc
