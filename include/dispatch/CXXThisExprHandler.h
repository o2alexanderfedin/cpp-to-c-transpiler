/**
 * @file CXXThisExprHandler.h
 * @brief Handler for CXXThisExpr (this pointer)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXThisExprHandler
 * @brief Translates C++ this pointer to C explicit this parameter
 *
 * CXXThisExpr represents the 'this' pointer in C++ member functions.
 * For C transpilation, we convert it to a reference to the explicit
 * 'this' parameter that we add to translated C functions.
 */
class CXXThisExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXThisExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
