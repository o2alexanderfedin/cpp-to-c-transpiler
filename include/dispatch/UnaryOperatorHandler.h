/**
 * @file UnaryOperatorHandler.h
 * @brief Handler for unary operator expressions (!, -, ++, --, *, &, etc.)
 *
 * Implements Chain of Responsibility pattern for dispatching UnaryOperator nodes.
 * Handles: Logical, arithmetic, increment/decrement, pointer, reference operators
 *
 * Design Principles:
 * - Single Responsibility: Only handles unary operator translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Recursive Dispatch: Dispatches operand subexpression through dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class UnaryOperatorHandler
 * @brief Translates C++ unary operators to C unary operators
 *
 * Handles all unary operators:
 * - Logical: !
 * - Arithmetic: -, +
 * - Increment/Decrement: ++, -- (prefix and postfix)
 * - Pointer: *, &
 * - Bitwise: ~
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Extract operand subexpression
 * 2. Dispatch operand via dispatcher (recursive)
 * 3. Retrieve translated operand from ExprMapper
 * 4. Create C UnaryOperator with translated operand
 * 5. Store in ExprMapper
 */
class UnaryOperatorHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a UnaryOperator
     * @param E Expression to check
     * @return true if E is UnaryOperator, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle UnaryOperator translation with recursive dispatch
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E UnaryOperator to translate
     *
     * Recursively dispatches operand, then creates C UnaryOperator.
     */
    static void handleUnaryOperator(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
