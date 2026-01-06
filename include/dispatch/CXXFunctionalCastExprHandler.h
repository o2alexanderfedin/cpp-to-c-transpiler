/**
 * @file CXXFunctionalCastExprHandler.h
 * @brief Handler for CXXFunctionalCastExpr (functional-style casts)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXFunctionalCastExprHandler
 * @brief Handles C++ functional-style cast expressions
 *
 * CXXFunctionalCastExpr represents functional-style casts: Type(expr)
 * For C translation, we convert to C-style cast: (Type)expr
 */
class CXXFunctionalCastExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXFunctionalCastExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
