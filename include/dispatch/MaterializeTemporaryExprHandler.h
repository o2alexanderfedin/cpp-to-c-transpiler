/**
 * @file MaterializeTemporaryExprHandler.h
 * @brief Handler for MaterializeTemporaryExpr (C++ temporary object materialization)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class MaterializeTemporaryExprHandler
 * @brief Translates C++ MaterializeTemporaryExpr to C by unwrapping to subexpression
 *
 * MaterializeTemporaryExpr is a C++ wrapper that creates a temporary object with
 * extended lifetime. In C, we don't have this concept, so we simply unwrap to the
 * subexpression.
 */
class MaterializeTemporaryExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleMaterializeTemporaryExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
