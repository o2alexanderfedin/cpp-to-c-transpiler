/**
 * @file CXXMemberCallExprHandler.h
 * @brief Handler for CXXMemberCallExpr (member function calls)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXMemberCallExprHandler
 * @brief Handles C++ member function calls
 *
 * CXXMemberCallExpr represents calls to member functions: obj.method(args)
 * For C translation, we convert to function calls with explicit 'this' parameter.
 */
class CXXMemberCallExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXMemberCallExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
