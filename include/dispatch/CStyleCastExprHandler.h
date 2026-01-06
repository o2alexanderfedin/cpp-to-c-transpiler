/**
 * @file CStyleCastExprHandler.h
 * @brief Handler for CStyleCastExpr (C-style casts)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @class CStyleCastExprHandler
 * @brief Handles C-style cast expressions
 *
 * CStyleCastExpr represents C-style casts: (Type)expr
 * These are already valid in C, so we just process the subexpression
 * and preserve the cast.
 */
class CStyleCastExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCStyleCastExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
