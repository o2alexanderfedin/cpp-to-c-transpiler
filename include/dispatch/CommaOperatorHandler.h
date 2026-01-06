/**
 * @file CommaOperatorHandler.h
 * @brief Handler for comma operator expressions (,)
 *
 * Implements Chain of Responsibility pattern for dispatching comma operator nodes.
 * Handles: Sequential expression evaluation with comma operator
 *
 * Design Principles:
 * - Single Responsibility: Only handles comma operator translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Recursive Dispatch: Dispatches LHS and RHS subexpressions through dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class CommaOperatorHandler
 * @brief Translates C++ comma operators to C comma operators
 *
 * Handles comma operator:
 * - Sequential evaluation: (a, b, c) - evaluates a, then b, then c, returns c
 * - For-loop multi-initialization: for (int i=0, j=10; ...)
 * - For-loop multi-increment: for (...; ...; i++, j--)
 *
 * The comma operator evaluates its LHS, discards the result, evaluates RHS,
 * and returns the RHS value. This is a binary operator with special semantics.
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Extract LHS and RHS subexpressions
 * 2. Dispatch LHS via dispatcher (recursive)
 * 3. Dispatch RHS via dispatcher (recursive)
 * 4. Retrieve translated LHS from ExprMapper
 * 5. Retrieve translated RHS from ExprMapper
 * 6. Create C BinaryOperator with BO_Comma opcode
 * 7. Store in ExprMapper
 */
class CommaOperatorHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a BinaryOperator with BO_Comma opcode
     * @param E Expression to check
     * @return true if E is BinaryOperator with BO_Comma, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle comma operator translation with recursive dispatch
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E BinaryOperator with BO_Comma opcode to translate
     *
     * Recursively dispatches LHS and RHS, then creates C BinaryOperator with BO_Comma.
     */
    static void handleCommaOperator(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
