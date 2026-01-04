/**
 * @file CompoundLiteralExprHandler.cpp
 * @brief Implementation of CompoundLiteralExprHandler
 */

#include "dispatch/CompoundLiteralExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CompoundLiteralExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CompoundLiteralExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CompoundLiteralExprHandler::handleCompoundLiteralExpr)
    );
}

bool CompoundLiteralExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CompoundLiteralExprClass;
}

void CompoundLiteralExprHandler::handleCompoundLiteralExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::CompoundLiteralExprClass && "Must be CompoundLiteralExpr");

    const auto* compoundLit = llvm::cast<clang::CompoundLiteralExpr>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CompoundLiteralExprHandler] CompoundLiteralExpr already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CompoundLiteralExprHandler] Processing CompoundLiteralExpr (pass-through)\n";

    // CompoundLiteralExpr is already valid C, but we need to dispatch the initializer
    const clang::Expr* init = compoundLit->getInitializer();

    llvm::outs() << "[CompoundLiteralExprHandler] Dispatching initializer\n";
    bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(init));

    if (!handled) {
        llvm::errs() << "[CompoundLiteralExprHandler] ERROR: Initializer not handled\n";
        assert(false && "Initializer must be handled");
    }

    // Get translated initializer
    clang::Expr* cInit = exprMapper.getCreated(init);
    assert(cInit && "Initializer must be in ExprMapper");

    // Create new CompoundLiteralExpr with translated initializer
    clang::CompoundLiteralExpr* cCompoundLit = new (cASTContext) clang::CompoundLiteralExpr(
        compoundLit->getLParenLoc(),
        cASTContext.getTrivialTypeSourceInfo(compoundLit->getType()),
        compoundLit->getType(),
        compoundLit->getValueKind(),
        cInit,
        compoundLit->isFileScope()
    );

    llvm::outs() << "[CompoundLiteralExprHandler] Created C CompoundLiteralExpr\n";

    // Store in ExprMapper
    exprMapper.setCreated(E, cCompoundLit);
}

} // namespace cpptoc
