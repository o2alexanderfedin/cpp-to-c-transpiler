/**
 * @file DeclRefExprHandler.h
 * @brief Handler for declaration reference expressions (variable/function references)
 *
 * Implements Chain of Responsibility pattern for dispatching DeclRefExpr nodes.
 * Handles: References to variables, parameters, functions
 *
 * Design Principles:
 * - Single Responsibility: Only handles declaration reference translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class DeclRefExprHandler
 * @brief Translates C++ declaration references to C declaration references
 *
 * Handles DeclRefExpr nodes that reference:
 * - Variables (local, global)
 * - Parameters
 * - Functions
 * - Enum constants
 *
 * DeclRefExpr has no subexpressions, so no recursive dispatch needed.
 */
class DeclRefExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a DeclRefExpr
     * @param E Expression to check
     * @return true if E is DeclRefExpr, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle DeclRefExpr translation
     * @param disp Dispatcher (for accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E DeclRefExpr to translate
     *
     * Creates C DeclRefExpr node and stores in ExprMapper.
     */
    static void handleDeclRefExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
