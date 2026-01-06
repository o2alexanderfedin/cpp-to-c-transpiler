/**
 * @file ConstantExprHandler.h
 * @brief Handler for constant expressions (C++17+ wrapper for constant evaluation)
 *
 * Implements Chain of Responsibility pattern for dispatching ConstantExpr nodes.
 * ConstantExpr is a wrapper node introduced in C++17 that wraps expressions that
 * are known to be constant at compile time (e.g., enum constants in case labels).
 *
 * Design Principles:
 * - Single Responsibility: Only handles ConstantExpr unwrapping
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class ConstantExprHandler
 * @brief Translates C++ ConstantExpr to C by unwrapping and dispatching subexpression
 *
 * ConstantExpr is a C++17+ wrapper that indicates an expression is constant.
 * In C, we don't have this wrapper, so we simply unwrap it and dispatch the
 * subexpression (which is typically a DeclRefExpr, IntegerLiteral, etc.).
 *
 * Example:
 * C++: case GameState::Menu: // wrapped in ConstantExpr
 * C:   case GameState__Menu: // unwrapped DeclRefExpr
 */
class ConstantExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a ConstantExpr
     * @param E Expression to check
     * @return true if E is ConstantExpr, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle ConstantExpr translation
     * @param disp Dispatcher (for accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E ConstantExpr to translate
     *
     * Unwraps the ConstantExpr and dispatches the subexpression.
     */
    static void handleConstantExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
