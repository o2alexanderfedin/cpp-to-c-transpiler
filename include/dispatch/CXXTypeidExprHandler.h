/**
 * @file CXXTypeidExprHandler.h
 * @brief Handler for C++ typeid() operator (CXXTypeidExpr) with TypeidTranslator integration
 *
 * Implements Chain of Responsibility pattern for dispatching CXXTypeidExpr nodes
 * to TypeidTranslator for translation to C type_info retrieval.
 *
 * Design Principles:
 * - Single Responsibility: Only handles CXXTypeidExpr translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Delegation: Delegates to TypeidTranslator for actual translation
 * - Recursive Dispatch: Dispatches expression operands through dispatcher
 *
 * ## C++ typeid() Operator
 *
 * The typeid operator provides runtime type information (RTTI) in two forms:
 * - **Polymorphic**: `typeid(*ptr)` - Queries vtable at runtime for dynamic type
 * - **Static**: `typeid(Type)` or `typeid(obj)` - Resolved at compile time
 *
 * This handler detects CXXTypeidExpr nodes and delegates translation to TypeidTranslator.
 *
 * ## Integration with TypeidTranslator
 *
 * This handler is the dispatcher-side integration point for TypeidTranslator.
 * Flow:
 * 1. Dispatcher detects CXXTypeidExpr
 * 2. Handler checks if polymorphic (via TypeidTranslator::isPolymorphicTypeid)
 * 3. If polymorphic, recursively dispatch expression operand
 * 4. Handler delegates to TypeidTranslator::translateTypeid()
 * 5. TypeidTranslator returns C expression string
 * 6. Handler creates C expression from string
 * 7. Handler stores result in ExprMapper
 *
 * ## Translation Patterns
 *
 * **Polymorphic typeid (vtable lookup)**:
 * ```cpp
 * // C++ Code:
 * Base* ptr = new Derived();
 * const std::type_info& ti = typeid(*ptr);
 *
 * // Translated C:
 * struct Base* ptr = Derived_new();
 * const struct __class_type_info* ti = ((const struct __class_type_info**)ptr->vptr)[-1];
 * ```
 *
 * **Static typeid (compile-time constant)**:
 * ```cpp
 * // C++ Code:
 * const std::type_info& ti = typeid(Base);
 *
 * // Translated C:
 * const struct __class_type_info* ti = &__ti_Base;
 * ```
 *
 * **Static typeid with object (non-polymorphic)**:
 * ```cpp
 * // C++ Code:
 * Base b;  // Non-polymorphic
 * const std::type_info& ti = typeid(b);
 *
 * // Translated C:
 * struct Base b;
 * const struct __class_type_info* ti = &__ti_Base;
 * ```
 *
 * ## WHY This Matters
 *
 * RTTI via typeid() is fundamental for:
 * - Debugging: Runtime type inspection
 * - Serialization: Storing/loading polymorphic objects
 * - Reflection: Dynamic type-based dispatch
 * - Type comparison: `if (typeid(*a) == typeid(*b))`
 *
 * Without this handler, C++ code using RTTI cannot transpile correctly.
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXTypeidExprHandler
 * @brief Translates C++ typeid() operator (CXXTypeidExpr) to C type_info retrieval
 *
 * Handles both polymorphic and static typeid by delegating to TypeidTranslator.
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Detect CXXTypeidExpr
 * 2. Check if polymorphic (via TypeidTranslator::isPolymorphicTypeid)
 * 3. If polymorphic, dispatch expression operand recursively
 * 4. Delegate to TypeidTranslator::translateTypeid()
 * 5. Create C expression from translation result
 * 6. Store C expression in ExprMapper
 *
 * Translation decisions:
 * - Polymorphic typeid: Requires vtable lookup at runtime
 *   * Expression operand must be dispatched
 *   * Result is vtable dereference: `((const struct __class_type_info**)ptr->vptr)[-1]`
 * - Static typeid: Compile-time constant reference
 *   * Type operand requires no dispatch
 *   * Result is static reference: `&__ti_ClassName`
 */
class CXXTypeidExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a CXXTypeidExpr
     * @param E Expression to check
     * @return true if E is CXXTypeidExpr, false otherwise
     *
     * Uses exact type matching with getStmtClass() for correctness.
     * Rejects CallExpr, BinaryOperator, UnaryOperator, etc.
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle CXXTypeidExpr translation with TypeidTranslator integration
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E CXXTypeidExpr to translate
     *
     * Flow:
     * 1. Cast E to CXXTypeidExpr
     * 2. Check ExprMapper for existing translation (prevent duplication)
     * 3. Check if polymorphic (via TypeidTranslator::isPolymorphicTypeid)
     * 4. If polymorphic, recursively dispatch expression operand
     * 5. Delegate to TypeidTranslator::translateTypeid()
     * 6. Create C expression from translation result
     * 7. Store C expression in ExprMapper
     *
     * Logs detailed debug information for troubleshooting.
     */
    static void handleTypeidExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );

private:
    /**
     * @brief Dispatch expression operand recursively
     * @param disp Dispatcher for recursive dispatch
     * @param cppASTContext C++ ASTContext
     * @param cASTContext C ASTContext
     * @param typeidExpr CXXTypeidExpr with expression operand
     *
     * Used for polymorphic typeid: `typeid(*ptr)`
     * Dispatches the expression operand (*ptr) to ensure it's translated.
     */
    static void dispatchOperand(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::CXXTypeidExpr* typeidExpr
    );

    /**
     * @brief Create C expression from TypeidTranslator result
     * @param cASTContext Target C ASTContext
     * @param translationStr C code string from TypeidTranslator
     * @param resultType Type of the result expression
     * @return C expression representing the translation
     *
     * NOTE: Current implementation creates a StringLiteral as placeholder.
     * Future enhancement: Parse translationStr and create proper AST nodes
     * (DeclRefExpr for static, complex expression for polymorphic).
     */
    static clang::Expr* createCExprFromString(
        clang::ASTContext& cASTContext,
        const std::string& translationStr,
        clang::QualType resultType
    );
};

} // namespace cpptoc
