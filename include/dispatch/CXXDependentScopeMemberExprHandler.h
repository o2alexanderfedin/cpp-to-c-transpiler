/**
 * @file CXXDependentScopeMemberExprHandler.h
 * @brief Handler for template-dependent member expressions
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXDependentScopeMemberExprHandler
 * @brief Translates CXXDependentScopeMemberExpr to C member access
 *
 * CXXDependentScopeMemberExpr appears in template-dependent contexts.
 * For C transpilation, we convert it to a regular MemberExpr.
 */
class CXXDependentScopeMemberExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXDependentScopeMemberExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
