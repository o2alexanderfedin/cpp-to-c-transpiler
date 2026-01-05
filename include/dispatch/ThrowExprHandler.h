/**
 * @file ThrowExprHandler.h
 * @brief Handler for C++ throw expressions (CXXThrowExpr)
 *
 * Implements Chain of Responsibility pattern for dispatching throw expressions.
 * Handles: CXXThrowExpr (throw statements)
 *
 * Design Principles:
 * - Single Responsibility: Only handles throw expression translation
 * - Delegation: Delegates to ThrowTranslator service class for implementation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class ThrowExprHandler
 * @brief Translates C++ throw expressions to C exception runtime calls
 *
 * CXXThrowExpr represents throw statements:
 * - throw Error("message");
 * - throw IntError(42);
 * - throw; (re-throw)
 *
 * Delegates to ThrowTranslator service class for implementation.
 */
class ThrowExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(::CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a throw expression
     * @param E Expression to check
     * @return true if E is CXXThrowExpr, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle throw expression translation
     * @param disp Dispatcher (for recursive dispatch and accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E CXXThrowExpr to translate
     *
     * Delegates to ThrowTranslator to generate C code for:
     * 1. Exception object allocation
     * 2. Constructor call
     * 3. cxx_throw runtime call
     */
    static void handleThrowExpr(
        const ::CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
