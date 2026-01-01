/**
 * @file CallExprHandler.h
 * @brief Handler for regular C/C++ function calls (CallExpr)
 *
 * Implements Chain of Responsibility pattern for dispatching CallExpr nodes
 * to translate regular function calls from C++ to C.
 *
 * Design Principles:
 * - Single Responsibility: Only handles CallExpr translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Recursive Dispatch: Dispatches all function arguments through dispatcher
 *
 * ## CallExpr vs CXXOperatorCallExpr
 *
 * CRITICAL distinction:
 * - CallExpr: Regular function calls (e.g., `add(3, 4)`, `printf("hello")`)
 * - CXXOperatorCallExpr: User-defined operator overloading (e.g., `obj[5]`)
 *
 * This handler only handles CallExpr (regular function calls).
 * Operator overloading is handled by CXXOperatorCallExprHandler.
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @class CallExprHandler
 * @brief Translates regular function calls (CallExpr) from C++ to C
 *
 * Handles regular function calls by:
 * 1. Detecting CallExpr nodes
 * 2. Dispatching the callee expression (function reference)
 * 3. Dispatching all argument expressions recursively
 * 4. Creating C CallExpr with translated callee and arguments
 * 5. Storing result in ExprMapper
 */
class CallExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a CallExpr
     * @param E Expression to check
     * @return true if E is CallExpr (but not CXXOperatorCallExpr), false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle CallExpr translation
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E CallExpr to translate
     *
     * Flow:
     * 1. Cast E to CallExpr
     * 2. Check ExprMapper for existing translation (prevent duplication)
     * 3. Dispatch callee expression (function reference)
     * 4. Dispatch all argument expressions recursively
     * 5. Create C CallExpr with translated callee and arguments
     * 6. Store C CallExpr in ExprMapper
     */
    static void handleCallExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
