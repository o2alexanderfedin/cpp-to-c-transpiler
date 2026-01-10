/**
 * @file ConditionalOperatorHandler.h
 * @brief Handler for ConditionalOperator (ternary operator)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @class ConditionalOperatorHandler
 * @brief Translates C++ conditional operator (ternary) to C
 *
 * ConditionalOperator represents the ternary operator: condition ? true_expr : false_expr
 * This operator exists in both C++ and C, so translation is straightforward.
 */
class ConditionalOperatorHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Expr* E);

    static void handleConditionalOperator(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
