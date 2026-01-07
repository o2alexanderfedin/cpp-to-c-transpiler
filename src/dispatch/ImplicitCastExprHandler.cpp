/**
 * @file ImplicitCastExprHandler.cpp
 * @brief Implementation of ImplicitCastExprHandler dispatcher pattern
 */

#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/TypeHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ImplicitCastExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to ExprPredicate and ExprVisitor to avoid ambiguity
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&ImplicitCastExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&ImplicitCastExprHandler::handleImplicitCast)
    );
}

bool ImplicitCastExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::ImplicitCastExprClass;
}

void ImplicitCastExprHandler::handleImplicitCast(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Expression must be ImplicitCastExpr");

    const auto* cppCast = llvm::cast<clang::ImplicitCastExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(cppCast)) {
        llvm::outs() << "[ImplicitCastExprHandler] ImplicitCastExpr already translated, skipping\n";
        return;
    }

    // Extract subexpression (the expression being cast)
    const clang::Expr* cppSubExpr = cppCast->getSubExpr();
    assert(cppSubExpr && "ImplicitCastExpr must have subexpression");

    llvm::outs() << "[ImplicitCastExprHandler] Processing ImplicitCastExpr with cast kind: "
                 << cppCast->getCastKindName() << "\n";

    // CRITICAL: Dispatch subexpression via dispatcher (recursive)
    llvm::outs() << "[ImplicitCastExprHandler] Dispatching subexpression\n";
    bool subExprHandled = disp.dispatch(
        cppASTContext,
        cASTContext,
        const_cast<clang::Expr*>(cppSubExpr)
    );

    // Retrieve translated subexpression from ExprMapper
    clang::Expr* cSubExpr = exprMapper.getCreated(cppSubExpr);

    if (!cSubExpr) {
        llvm::errs() << "[ImplicitCastExprHandler] ERROR: Failed to retrieve translated subexpression\n";
        llvm::errs() << "  Subexpression type: " << cppSubExpr->getStmtClassName() << "\n";
        llvm::errs() << "  Was handled: " << (subExprHandled ? "yes" : "no") << "\n";
        assert(false && "ImplicitCastExpr subexpression must be translated");
    }

    llvm::outs() << "[ImplicitCastExprHandler] Subexpression translated successfully\n";

    // Translate type from C++ to C ASTContext
    clang::QualType cType = TypeHandler::translateType(cppCast->getType(), cppASTContext, cASTContext);

    // Create C ImplicitCastExpr with translated subexpression and type
    // Note: ImplicitCastExpr::Create requires cast kind, type, subexpression, and FP options
    clang::ImplicitCastExpr* cCast = clang::ImplicitCastExpr::Create(
        cASTContext,
        cType,                         // Use translated C type
        cppCast->getCastKind(),        // Keep same cast kind
        cSubExpr,                      // Translated subexpression
        nullptr,                       // No base path (for class casts)
        cppCast->getValueKind(),       // Keep same value kind (lvalue, rvalue, etc.)
        clang::FPOptionsOverride()     // Default floating-point options
    );

    assert(cCast && "Failed to create C ImplicitCastExpr");

    llvm::outs() << "[ImplicitCastExprHandler] Created C ImplicitCastExpr with cast kind: "
                 << cCast->getCastKindName() << "\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(cppCast, cCast);
}

} // namespace cpptoc
