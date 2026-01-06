/**
 * @file RecoveryExprHandler.h
 * @brief Handler for RecoveryExpr (error recovery expressions)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @class RecoveryExprHandler
 * @brief Handles RecoveryExpr nodes created during error recovery
 *
 * RecoveryExpr is created by Clang when it encounters syntax errors
 * or incomplete code during parsing. For C transpilation, we create
 * a placeholder expression.
 */
class RecoveryExprHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleRecoveryExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
