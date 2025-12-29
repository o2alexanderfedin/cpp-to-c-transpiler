/**
 * @file ParenExprHandler.cpp
 * @brief Implementation of ParenExprHandler dispatcher pattern
 */

#include "dispatch/ParenExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ParenExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to ExprPredicate and ExprVisitor to avoid ambiguity
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&ParenExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&ParenExprHandler::handleParenExpr)
    );
}

bool ParenExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::ParenExprClass;
}

void ParenExprHandler::handleParenExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Expression must be ParenExpr");

    const auto* cppParen = llvm::cast<clang::ParenExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreatedExpr(cppParen)) {
        llvm::outs() << "[ParenExprHandler] ParenExpr already translated, skipping\n";
        return;
    }

    // Extract inner expression (the expression inside the parentheses)
    const clang::Expr* cppInnerExpr = cppParen->getSubExpr();
    assert(cppInnerExpr && "ParenExpr must have inner expression");

    llvm::outs() << "[ParenExprHandler] Processing ParenExpr\n";

    // CRITICAL: Dispatch inner expression via dispatcher (recursive)
    llvm::outs() << "[ParenExprHandler] Dispatching inner expression\n";
    bool innerHandled = disp.dispatch(
        cppASTContext,
        cASTContext,
        const_cast<clang::Expr*>(cppInnerExpr)
    );

    // Retrieve translated inner expression from ExprMapper
    clang::Expr* cInnerExpr = exprMapper.getCreatedExpr(cppInnerExpr);

    if (!cInnerExpr) {
        llvm::errs() << "[ParenExprHandler] ERROR: Failed to retrieve translated inner expression\n";
        llvm::errs() << "  Inner expression type: " << cppInnerExpr->getStmtClassName() << "\n";
        llvm::errs() << "  Was handled: " << (innerHandled ? "yes" : "no") << "\n";
        assert(false && "ParenExpr inner expression must be translated");
    }

    llvm::outs() << "[ParenExprHandler] Inner expression translated successfully\n";

    // Create C ParenExpr with translated inner expression
    clang::ParenExpr* cParen = new (cASTContext) clang::ParenExpr(
        clang::SourceLocation(),  // L paren location
        clang::SourceLocation(),  // R paren location
        cInnerExpr                // Translated inner expression
    );

    assert(cParen && "Failed to create C ParenExpr");

    llvm::outs() << "[ParenExprHandler] Created C ParenExpr\n";

    // Store mapping in ExprMapper
    exprMapper.setCreatedExpr(cppParen, cParen);
}

} // namespace cpptoc
