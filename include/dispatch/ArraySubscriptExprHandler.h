/**
 * @file ArraySubscriptExprHandler.h
 * @brief Handler for array subscript expressions ([] operator)
 *
 * Implements Chain of Responsibility pattern for dispatching ArraySubscriptExpr nodes.
 * Handles: Single and multi-dimensional array access, pointer indexing
 *
 * Design Principles:
 * - Single Responsibility: Only handles array subscript translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Recursive Dispatch: Dispatches base and index subexpressions through dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class ArraySubscriptExprHandler
 * @brief Translates C++ array subscript expressions to C array subscript expressions
 *
 * Handles array element access:
 * - Single dimension: arr[5]
 * - Multi-dimensional: matrix[row][col] (nested ArraySubscriptExpr)
 * - Pointer arithmetic: ptr[i] (equivalent to *(ptr + i))
 * - Complex base: getArray()[index]
 * - Complex index: arr[i + j * 2]
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Extract base expression (the array being indexed)
 * 2. Extract index expression (the subscript)
 * 3. Dispatch base via dispatcher (recursive)
 * 4. Dispatch index via dispatcher (recursive)
 * 5. Retrieve translated base from ExprMapper
 * 6. Retrieve translated index from ExprMapper
 * 7. Create C ArraySubscriptExpr with translated operands
 * 8. Store in ExprMapper
 *
 * WHY this pattern matters:
 * - Array subscript syntax is identical in C++ and C, but subexpressions may differ
 * - Base can be any expression returning array/pointer (function call, member access, etc.)
 * - Index can be any integral expression (literals, variables, complex arithmetic)
 * - Multi-dimensional arrays are represented as nested ArraySubscriptExpr nodes
 * - Recursive dispatch ensures all subexpressions are properly translated
 *
 * Example translation:
 * C++: matrix[i + 1][j * 2]
 * AST: ArraySubscriptExpr(ArraySubscriptExpr(matrix, i+1), j*2)
 * C:   matrix[i + 1][j * 2] (same syntax, all subexpressions translated)
 */
class ArraySubscriptExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is an ArraySubscriptExpr
     * @param E Expression to check
     * @return true if E is ArraySubscriptExpr, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle ArraySubscriptExpr translation with recursive dispatch
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E ArraySubscriptExpr to translate
     *
     * Recursively dispatches base and index, then creates C ArraySubscriptExpr.
     *
     * Special handling:
     * - Base expression: Can be DeclRefExpr, CallExpr, MemberExpr, or nested ArraySubscriptExpr
     * - Index expression: Can be IntegerLiteral, DeclRefExpr, BinaryOperator, etc.
     * - Type preservation: Maintains array element type
     * - Multi-dimensional: Natural nesting of ArraySubscriptExpr nodes
     */
    static void handleArraySubscript(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
