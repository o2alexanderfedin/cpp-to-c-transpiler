/**
 * @file MaterializeTemporaryExprHandler.cpp
 * @brief Implementation of MaterializeTemporaryExprHandler
 */

#include "dispatch/MaterializeTemporaryExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void MaterializeTemporaryExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&MaterializeTemporaryExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&MaterializeTemporaryExprHandler::handleMaterializeTemporaryExpr)
    );
}

bool MaterializeTemporaryExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::MaterializeTemporaryExprClass;
}

void MaterializeTemporaryExprHandler::handleMaterializeTemporaryExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Expression must be MaterializeTemporaryExpr");

    const auto* cppMaterialize = llvm::cast<clang::MaterializeTemporaryExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(cppMaterialize)) {
        llvm::outs() << "[MaterializeTemporaryExprHandler] Already translated, skipping\\n";
        return;
    }

    llvm::outs() << "[MaterializeTemporaryExprHandler] Processing MaterializeTemporaryExpr\\n";
    llvm::outs() << "[MaterializeTemporaryExprHandler] Note: C doesn't have temporary lifetime extension, unwrapping to subexpression\\n";

    // Extract subexpression
    const clang::Expr* cppSubExpr = cppMaterialize->getSubExpr();
    assert(cppSubExpr && "MaterializeTemporaryExpr must have subexpression");

    // Dispatch subexpression
    llvm::outs() << "[MaterializeTemporaryExprHandler] Dispatching subexpression (type: "
                 << cppSubExpr->getStmtClassName() << ")\\n";
    bool subExprHandled = disp.dispatch(
        cppASTContext,
        cASTContext,
        const_cast<clang::Expr*>(cppSubExpr)
    );

    // Retrieve translated subexpression
    clang::Expr* cSubExpr = exprMapper.getCreated(cppSubExpr);

    if (!cSubExpr) {
        llvm::errs() << "[MaterializeTemporaryExprHandler] ERROR: Failed to retrieve translated subexpression\\n";
        llvm::errs() << "  Subexpression type: " << cppSubExpr->getStmtClassName() << "\\n";
        llvm::errs() << "  Was handled: " << (subExprHandled ? "yes" : "no") << "\\n";
        assert(false && "MaterializeTemporaryExpr subexpression must be translated");
    }

    llvm::outs() << "[MaterializeTemporaryExprHandler] Subexpression translated successfully\\n";

    // Map MaterializeTemporaryExpr directly to translated subexpression (transparent unwrap)
    llvm::outs() << "[MaterializeTemporaryExprHandler] Mapping MaterializeTemporaryExpr to subexpression (transparent unwrap)\\n";
    exprMapper.setCreated(cppMaterialize, cSubExpr);

    llvm::outs() << "[MaterializeTemporaryExprHandler] MaterializeTemporaryExpr successfully unwrapped\\n";
}

} // namespace cpptoc
