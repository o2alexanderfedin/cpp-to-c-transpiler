/**
 * @file ExprWithCleanupsHandler.h
 * @brief Handler for expressions with cleanup actions
 *
 * Implements Chain of Responsibility pattern for dispatching ExprWithCleanups expressions.
 * Handles: ExprWithCleanups (C++ expressions that require cleanup - destructors, temporaries, etc.)
 *
 * Design Principles:
 * - Single Responsibility: Only handles ExprWithCleanups translation
 * - Recursive Dispatch: Dispatches subexpression via dispatcher
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class ExprWithCleanupsHandler
 * @brief Translates C++ ExprWithCleanups to C by unwrapping to subexpression
 *
 * ExprWithCleanups is a C++ wrapper expression that indicates cleanup operations
 * (destructors, exception handling, etc.) need to run after the subexpression.
 *
 * In C, we don't have RAII or destructors, so we simply unwrap and use the
 * subexpression directly. This is a transparent pass-through handler.
 *
 * Example C++ code:
 * ```cpp
 * std::string getName() { return "test"; }
 * int len = getName().length();  // ExprWithCleanups wraps the call
 * ```
 *
 * The getName() call creates a temporary that needs cleanup (destructor call).
 * In C, we would have already transformed this to manual memory management,
 * so we just unwrap to the actual expression.
 */
class ExprWithCleanupsHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is ExprWithCleanups
     * @param E Expression to check
     * @return true if E is ExprWithCleanups, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle ExprWithCleanups expression translation
     * @param disp Dispatcher (for recursive dispatch and accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E ExprWithCleanups to translate
     *
     * Recursively dispatches subexpression, retrieves from ExprMapper,
     * and maps the ExprWithCleanups directly to the translated subexpression.
     * This effectively "unwraps" the cleanup wrapper since C doesn't have RAII.
     */
    static void handleExprWithCleanups(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
