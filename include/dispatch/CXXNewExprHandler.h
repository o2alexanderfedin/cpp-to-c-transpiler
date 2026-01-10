/**
 * @file CXXNewExprHandler.h
 * @brief Handler for CXXNewExpr (new expressions)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXNewExprHandler
 * @brief Handles C++ new expressions
 *
 * CXXNewExpr represents new expressions: new Type() or new Type[size]
 * For C translation, we convert to malloc() calls.
 */
class CXXNewExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXNewExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
