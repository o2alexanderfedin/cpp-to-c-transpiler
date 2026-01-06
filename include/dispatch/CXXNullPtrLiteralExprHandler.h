/**
 * @file CXXNullPtrLiteralExprHandler.h
 * @brief Handler for CXXNullPtrLiteralExpr (nullptr literal)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXNullPtrLiteralExprHandler
 * @brief Translates C++ nullptr to C NULL
 *
 * CXXNullPtrLiteralExpr represents the C++11 nullptr keyword.
 * For C translation, we convert it to NULL (defined as (void*)0 or 0).
 */
class CXXNullPtrLiteralExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXNullPtrLiteralExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
