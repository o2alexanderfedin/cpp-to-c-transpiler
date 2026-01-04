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

    // Phase 3: Delegate to ThrowTranslator service class with dispatcher (string-based for now)
    // Phase 5 will refactor to return C AST nodes
    clang::ThrowTranslator translator;
    std::string throwCode = translator.generateThrowCode(throwExpr, disp, cppASTContext, cASTContext);

    llvm::outs() << "[ThrowExprHandler] Generated throw code (via dispatcher):\n" << throwCode << "\n";

    // TODO Phase 5: Store C Expr* in ExprMapper instead of string
    // For now, we don't have a C AST representation yet
    // The string will be used by parent statement handler

    llvm::outs() << "[ThrowExprHandler] CXXThrowExpr translation complete (string-based)\n";
}

} // namespace cpptoc
