/**
 * @file CXXDefaultArgExprHandler.h
 * @brief Handler for CXXDefaultArgExpr (default argument expressions)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXDefaultArgExprHandler
 * @brief Handles C++ default argument expressions
 *
 * CXXDefaultArgExpr represents a default argument value in a function call.
 * For C translation, we need to dispatch on the actual default value expression.
 */
class CXXDefaultArgExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXDefaultArgExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
