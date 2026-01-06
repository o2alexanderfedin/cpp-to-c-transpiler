/**
 * @file CXXOperatorCallExprHandler.h
 * @brief Handler for C++ operator overloading (CXXOperatorCallExpr) with SpecialOperatorTranslator integration
 *
 * Implements Chain of Responsibility pattern for dispatching CXXOperatorCallExpr nodes
 * to SpecialOperatorTranslator for translation to C function calls.
 *
 * Design Principles:
 * - Single Responsibility: Only handles CXXOperatorCallExpr translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Delegation: Delegates to SpecialOperatorTranslator for actual translation
 * - Recursive Dispatch: Dispatches all operator arguments through dispatcher
 *
 * ## CXXOperatorCallExpr vs Built-in Operators
 *
 * CRITICAL distinction:
 * - CXXOperatorCallExpr: User-defined operator overloading (e.g., `class Array { int& operator[](int); }`)
 * - BinaryOperator: Built-in operators on primitive types (e.g., `int a = 1 + 2;`)
 * - UnaryOperator: Built-in unary operators (e.g., `int b = -a;`)
 *
 * This handler only handles CXXOperatorCallExpr (overloaded operators).
 * Built-in operators are handled by BinaryOperatorHandler and UnaryOperatorHandler.
 *
 * ## Integration with SpecialOperatorTranslator
 *
 * This handler is the dispatcher-side integration point for SpecialOperatorTranslator.
 * Flow:
 * 1. Dispatcher detects CXXOperatorCallExpr
 * 2. This handler validates it's a special operator (via SpecialOperatorTranslator::isSpecialOperator)
 * 3. Handler recursively dispatches all arguments (including implicit `this`)
 * 4. Handler delegates to SpecialOperatorTranslator::transformCall()
 * 5. SpecialOperatorTranslator creates C CallExpr
 * 6. Handler stores result in ExprMapper
 *
 * ## Supported Special Operators (12 categories)
 *
 * 1. Instance subscript: `arr[5]` → `Array_operator_subscript(&arr, 5)`
 * 2. Instance call: `func(x)` → `Functor_operator_call(&func, x)`
 * 3. Smart pointer arrow: `ptr->field` → `SmartPtr_operator_arrow(&ptr)->field`
 * 4. Smart pointer deref: `*ptr` → `SmartPtr_operator_star(&ptr)`
 * 5. Stream output: `cout << obj` → `Class_operator_output(stdout, &obj)`
 * 6. Stream input: `cin >> obj` → `Class_operator_input(stdin, &obj)`
 * 7. Conversion: `(int)obj` → `Class_operator_to_int(&obj)`
 * 8. Bool conversion: `if (obj)` → `if (Class_operator_to_bool(&obj))`
 * 9. Copy assignment: `a = b` → `Class_operator_assign(&a, &b)`
 * 10. Move assignment: `a = move(b)` → `Class_operator_assign_move(&a, &b)`
 * 11. Address-of (rare): `&obj` → `Class_operator_addressof(&obj)`
 * 12. Comma (rare): `(a, b)` → `Class_operator_comma(&a, b)`
 *
 * ## WHY This Matters
 *
 * Operator overloading is fundamental to C++ but has no direct C equivalent.
 * This handler enables transparent translation of:
 * - Smart pointers (operator->, operator*, operator bool)
 * - Containers (operator[], operator())
 * - Stream I/O (operator<<, operator>>)
 * - Assignment semantics (operator=)
 *
 * Without this handler, real-world C++ code using these patterns cannot transpile.
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXOperatorCallExprHandler
 * @brief Translates C++ operator overloading (CXXOperatorCallExpr) to C function calls
 *
 * Handles all 12 special operator categories by delegating to SpecialOperatorTranslator.
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Detect CXXOperatorCallExpr
 * 2. Verify it's a special operator (not arithmetic/comparison handled elsewhere)
 * 3. Extract all arguments (includes implicit `this` as first argument)
 * 4. Dispatch all arguments recursively via dispatcher
 * 5. Retrieve translated arguments from ExprMapper
 * 6. Delegate to SpecialOperatorTranslator::transformCall()
 * 7. Store C CallExpr in ExprMapper
 *
 * Special cases:
 * - Conversion operators: May be wrapped in MaterializeTemporaryExpr
 * - Stream operators: Distinguish from bitwise shift (<<, >>)
 * - Assignment: Distinguish copy vs move
 */
class CXXOperatorCallExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a CXXOperatorCallExpr
     * @param E Expression to check
     * @return true if E is CXXOperatorCallExpr, false otherwise
     *
     * Uses exact type matching with getStmtClass() for correctness.
     * Rejects BinaryOperator, UnaryOperator, CallExpr, etc.
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle CXXOperatorCallExpr translation with SpecialOperatorTranslator integration
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E CXXOperatorCallExpr to translate
     *
     * Flow:
     * 1. Cast E to CXXOperatorCallExpr
     * 2. Check ExprMapper for existing translation (prevent duplication)
     * 3. Verify operator is special (via SpecialOperatorTranslator::isSpecialOperator)
     * 4. Recursively dispatch all arguments (implicit `this` + explicit args)
     * 5. Delegate to SpecialOperatorTranslator::transformCall()
     * 6. Store C CallExpr in ExprMapper
     *
     * Logs detailed debug information for troubleshooting.
     */
    static void handleOperatorCall(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );

private:
    /**
     * @brief Dispatch all operator arguments recursively
     * @param disp Dispatcher for recursive dispatch
     * @param cppASTContext C++ ASTContext
     * @param cASTContext C ASTContext
     * @param opCall CXXOperatorCallExpr with arguments to dispatch
     *
     * Dispatches all arguments including implicit `this` (first argument).
     * Verifies all arguments are successfully translated.
     */
    static void dispatchArguments(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::CXXOperatorCallExpr* opCall
    );
};

} // namespace cpptoc
