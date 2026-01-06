/**
 * @file ArraySubscriptExprHandler.cpp
 * @brief Implementation of ArraySubscriptExprHandler with recursive dispatch
 */

#include "dispatch/ArraySubscriptExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ArraySubscriptExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&ArraySubscriptExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&ArraySubscriptExprHandler::handleArraySubscript)
    );
}

bool ArraySubscriptExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::ArraySubscriptExprClass;
}

void ArraySubscriptExprHandler::handleArraySubscript(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::ArraySubscriptExprClass && "Must be ArraySubscriptExpr");

    const auto* cppArrSub = llvm::cast<clang::ArraySubscriptExpr>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[ArraySubscriptExprHandler] ArraySubscriptExpr already translated, skipping\n";
        return;
    }

    // Extract base and index subexpressions
    const clang::Expr* cppBase = cppArrSub->getBase();
    const clang::Expr* cppIdx = cppArrSub->getIdx();

    llvm::outs() << "[ArraySubscriptExprHandler] Processing ArraySubscriptExpr\n";

    // CRITICAL: Recursive dispatch pattern
    // Dispatch base via dispatcher (may trigger DeclRefExprHandler, ArraySubscriptExprHandler, CallExpr, etc.)
    llvm::outs() << "[ArraySubscriptExprHandler] Dispatching base expression\n";
    bool baseHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppBase));

    if (!baseHandled) {
        llvm::errs() << "[ArraySubscriptExprHandler] ERROR: Base not handled by any expression handler\n";
        assert(false && "Base must be handled");
    }

    // Retrieve translated base from ExprMapper
    clang::Expr* cBase = exprMapper.getCreated(cppBase);
    assert(cBase && "Base must be in ExprMapper after dispatch");

    // Dispatch index via dispatcher (recursive)
    llvm::outs() << "[ArraySubscriptExprHandler] Dispatching index expression\n";
    bool idxHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppIdx));

    if (!idxHandled) {
        llvm::errs() << "[ArraySubscriptExprHandler] ERROR: Index not handled by any expression handler\n";
        assert(false && "Index must be handled");
    }

    // Retrieve translated index from ExprMapper
    clang::Expr* cIdx = exprMapper.getCreated(cppIdx);
    assert(cIdx && "Index must be in ExprMapper after dispatch");

    llvm::outs() << "[ArraySubscriptExprHandler] Both base and index translated successfully\n";

    // Create C ArraySubscriptExpr with translated operands
    // Note: ArraySubscriptExpr constructor takes (lhs, rhs, type, valueKind, objectKind, rbracketloc)
    clang::ArraySubscriptExpr* cArrSub = new (cASTContext) clang::ArraySubscriptExpr(
        cBase,
        cIdx,
        cppArrSub->getType(),  // May need type translation in future
        cppArrSub->getValueKind(),
        cppArrSub->getObjectKind(),
        clang::SourceLocation()
    );

    llvm::outs() << "[ArraySubscriptExprHandler] Created C ArraySubscriptExpr\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, cArrSub);
}

} // namespace cpptoc
