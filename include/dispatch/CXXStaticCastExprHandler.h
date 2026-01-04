/**
 * @file CXXStaticCastExprHandler.h
 * @brief Handler for CXXStaticCastExpr (static_cast)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXStaticCastExprHandler
 * @brief Translates C++ static_cast to C cast
 *
 * CXXStaticCastExpr represents static_cast<T>(expr).
 * For C translation, we convert it to a C-style cast: (T)expr
 */
class CXXStaticCastExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXStaticCastExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
