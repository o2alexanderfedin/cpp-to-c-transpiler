/**
 * @file ParenExprHandler.h
 * @brief Handler for parenthesized expressions
 *
 * Implements Chain of Responsibility pattern for dispatching parenthesized expressions.
 * Handles: ParenExpr (expressions wrapped in parentheses like `(a + b)`)
 *
 * Design Principles:
 * - Single Responsibility: Only handles parenthesized expression translation
 * - Recursive Dispatch: Dispatches inner expression via dispatcher
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class ParenExprHandler
 * @brief Translates C++ parenthesized expressions to C parenthesized expressions
 *
 * ParenExpr represents expressions wrapped in parentheses:
 * - (a + b)
 * - ((x * y) + z)
 * - (variable)
 *
 * This is a pass-through handler that dispatches the inner expression
 * and wraps the result in C ParenExpr.
 */
class ParenExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a parenthesized expression
     * @param E Expression to check
     * @return true if E is ParenExpr, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle parenthesized expression translation
     * @param disp Dispatcher (for recursive dispatch and accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E ParenExpr to translate
     *
     * Recursively dispatches inner expression, retrieves from ExprMapper,
     * creates C ParenExpr with translated inner expression, stores in ExprMapper.
     */
    static void handleParenExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
