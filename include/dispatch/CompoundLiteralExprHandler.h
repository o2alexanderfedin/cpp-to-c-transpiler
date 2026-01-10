/**
 * @file CompoundLiteralExprHandler.h
 * @brief Handler for CompoundLiteralExpr pass-through
 *
 * CompoundLiteralExpr represents C99 compound literals like (struct T){a, b}.
 * These are created by CXXConstructExprHandler when translating C++ constructors.
 * This handler passes them through unchanged since they're already valid C.
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @class CompoundLiteralExprHandler
 * @brief Pass-through handler for CompoundLiteralExpr
 *
 * CompoundLiteralExpr is already valid C syntax, so we just pass it through.
 * However, we need to recursively dispatch the initializer expression inside it.
 */
class CompoundLiteralExprHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Check if this handler can handle the given expression
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle CompoundLiteralExpr by recursively dispatching initializer
     */
    static void handleCompoundLiteralExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
