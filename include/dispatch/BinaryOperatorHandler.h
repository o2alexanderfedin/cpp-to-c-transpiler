/**
 * @file BinaryOperatorHandler.h
 * @brief Handler for binary operator expressions (+, -, *, /, ==, etc.)
 *
 * Implements Chain of Responsibility pattern for dispatching BinaryOperator nodes.
 * Handles: Arithmetic, comparison, logical, bitwise, assignment operators
 *
 * Design Principles:
 * - Single Responsibility: Only handles binary operator translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Recursive Dispatch: Dispatches LHS and RHS subexpressions through dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class BinaryOperatorHandler
 * @brief Translates C++ binary operators to C binary operators
 *
 * Handles all binary operators:
 * - Arithmetic: +, -, *, /, %
 * - Comparison: ==, !=, <, >, <=, >=
 * - Logical: &&, ||
 * - Bitwise: &, |, ^, <<, >>
 * - Assignment: =, +=, -=, *=, /=, %=, &=, |=, ^=, <<=, >>=
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Extract LHS and RHS subexpressions
 * 2. Dispatch LHS via dispatcher (recursive)
 * 3. Dispatch RHS via dispatcher (recursive)
 * 4. Retrieve translated LHS from ExprMapper
 * 5. Retrieve translated RHS from ExprMapper
 * 6. Create C BinaryOperator with translated operands
 * 7. Store in ExprMapper
 */
class BinaryOperatorHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a BinaryOperator
     * @param E Expression to check
     * @return true if E is BinaryOperator, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle BinaryOperator translation with recursive dispatch
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E BinaryOperator to translate
     *
     * Recursively dispatches LHS and RHS, then creates C BinaryOperator.
     */
    static void handleBinaryOperator(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
