/**
 * @file CXXTemporaryObjectExprHandler.h
 * @brief Handler for CXXTemporaryObjectExpr (explicit temporary objects)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXTemporaryObjectExprHandler
 * @brief Translates C++ temporary object expressions to C compound literals
 *
 * CXXTemporaryObjectExpr represents explicit temporary object creation
 * like Vector3D(1, 2, 3). For C transpilation, we convert this to a
 * compound literal: (struct Vector3D){1, 2, 3}
 */
class CXXTemporaryObjectExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleCXXTemporaryObjectExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
