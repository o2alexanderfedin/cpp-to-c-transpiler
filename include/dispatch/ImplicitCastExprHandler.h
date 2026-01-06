/**
 * @file ImplicitCastExprHandler.h
 * @brief Handler for implicit cast expressions
 *
 * Implements Chain of Responsibility pattern for dispatching implicit cast expressions.
 * Handles: ImplicitCastExpr (automatic type conversions inserted by Clang)
 *
 * Design Principles:
 * - Single Responsibility: Only handles implicit cast translation
 * - Recursive Dispatch: Dispatches subexpression via dispatcher
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class ImplicitCastExprHandler
 * @brief Translates C++ implicit cast expressions to C implicit cast expressions
 *
 * Clang inserts ImplicitCastExpr nodes for type conversions:
 * - LValueToRValue (variable → value)
 * - IntegralCast (int → long, etc.)
 * - FunctionToPointerDecay (function → function pointer)
 * - ArrayToPointerDecay (array → pointer to first element)
 * - NoOp (no conversion, just type annotation)
 * - And many others
 *
 * Critical for expression translation - most expressions have implicit casts.
 */
class ImplicitCastExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is an implicit cast
     * @param E Expression to check
     * @return true if E is ImplicitCastExpr, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle implicit cast expression translation
     * @param disp Dispatcher (for recursive dispatch and accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E ImplicitCastExpr to translate
     *
     * Recursively dispatches subexpression, retrieves from ExprMapper,
     * creates C ImplicitCastExpr with translated subexpression, stores in ExprMapper.
     */
    static void handleImplicitCast(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
