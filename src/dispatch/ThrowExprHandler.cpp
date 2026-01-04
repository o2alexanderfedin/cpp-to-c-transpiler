/**
 * @file ThrowExprHandler.cpp
 * @brief Implementation of ThrowExprHandler dispatcher pattern
 */

#include "dispatch/ThrowExprHandler.h"
#include "ThrowTranslator.h"
#include "mapping/ExprMapper.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ThrowExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to ExprPredicate and ExprVisitor to match dispatcher interface
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&ThrowExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&ThrowExprHandler::handleThrowExpr)
    );
}

bool ThrowExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::CXXThrowExprClass;
}

void ThrowExprHandler::handleThrowExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Expression must be CXXThrowExpr");

    const auto* throwExpr = llvm::cast<clang::CXXThrowExpr>(E);

    llvm::outs() << "[ThrowExprHandler] Processing CXXThrowExpr\n";

    // Check if already processed
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
    if (exprMapper.hasCreated(throwExpr)) {
        llvm::outs() << "[ThrowExprHandler] CXXThrowExpr already translated, skipping\n";
        return;
    }

    // Phase 5: Delegate to ThrowTranslator service class (AST-based - COMPLETE)
    clang::ThrowTranslator translator;
    clang::CompoundStmt* throwStmt = translator.generateThrowCode(
        throwExpr, disp, cppASTContext, cASTContext
    );

    if (!throwStmt) {
        llvm::errs() << "[ThrowExprHandler] ERROR: ThrowTranslator returned null\n";
        return;
    }

    llvm::outs() << "[ThrowExprHandler] Generated throw AST with "
                 << throwStmt->size() << " statements\n";

    // Phase 5: Store C CompoundStmt* in ExprMapper (COMPLETE)
    // Note: CXXThrowExpr is an expression, but we translate it to a statement
    // The parent compound statement handler will incorporate this
    // For now, we treat the CompoundStmt as an expression-like construct
    exprMapper.setCreated(throwExpr, throwStmt);

    llvm::outs() << "[ThrowExprHandler] CXXThrowExpr translation complete (AST-based)\n";
}

} // namespace cpptoc
