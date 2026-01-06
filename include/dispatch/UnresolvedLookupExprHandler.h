/**
 * @file UnresolvedLookupExprHandler.h
 * @brief Handler for UnresolvedLookupExpr (unresolved function names)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class UnresolvedLookupExprHandler
 * @brief Handles UnresolvedLookupExpr nodes for unresolved function names
 *
 * UnresolvedLookupExpr represents a lookup that couldn't be resolved at parse time,
 * typically due to templates or dependent types. For C transpilation, we resolve
 * it to a simple DeclRefExpr.
 */
class UnresolvedLookupExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleUnresolvedLookupExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
