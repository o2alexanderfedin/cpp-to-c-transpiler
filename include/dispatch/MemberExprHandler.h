/**
 * @file MemberExprHandler.h
 * @brief Handler for member access expressions (obj.field and ptr->field)
 *
 * Implements Chain of Responsibility pattern for dispatching MemberExpr nodes.
 * Handles: Direct member access (.), indirect member access (->)
 *
 * Design Principles:
 * - Single Responsibility: Only handles member access translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Recursive Dispatch: Dispatches base expression through dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class MemberExprHandler
 * @brief Translates C++ member access expressions to C struct field access
 *
 * Handles member access expressions:
 * - Direct access: obj.field (using dot operator)
 * - Indirect access: ptr->field (using arrow operator)
 * - Nested access: obj.inner.field (recursive member access)
 * - Mixed access: ptr->inner.field (arrow then dot)
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Extract base expression (the object or pointer being accessed)
 * 2. Dispatch base via dispatcher (recursive)
 * 3. Retrieve translated base from ExprMapper
 * 4. Get member field declaration
 * 5. Create C MemberExpr with translated base and member
 * 6. Preserve arrow vs dot distinction (critical for C pointer semantics)
 * 7. Store in ExprMapper
 *
 * WHY recursive dispatch matters:
 * - Base can be any expression (DeclRefExpr, MemberExpr, CallExpr, etc.)
 * - Nested member access (obj.a.b.c) requires recursive translation
 * - ExprMapper prevents duplicate translation of shared subexpressions
 *
 * Arrow vs Dot preservation:
 * - C distinguishes obj.field (direct) from ptr->field (indirect)
 * - Must preserve isArrow() flag to maintain pointer semantics
 * - Incorrect flag produces invalid C code (obj->field or ptr.field)
 */
class MemberExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a MemberExpr
     * @param E Expression to check
     * @return true if E is MemberExpr, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle MemberExpr translation with recursive dispatch
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E MemberExpr to translate
     *
     * Recursively dispatches base expression, then creates C MemberExpr.
     * Preserves arrow vs dot distinction for correct C semantics.
     */
    static void handleMemberExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
