/**
 * @file CXXDynamicCastExprHandler.h
 * @brief Handler for C++ dynamic_cast<>() operator (CXXDynamicCastExpr) with DynamicCastTranslator integration
 *
 * Implements Chain of Responsibility pattern for dispatching CXXDynamicCastExpr nodes
 * to DynamicCastTranslator for translation to C runtime type checking.
 *
 * Design Principles:
 * - Single Responsibility: Only handles CXXDynamicCastExpr translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Delegation: Delegates to DynamicCastTranslator for actual translation
 * - Recursive Dispatch: Dispatches subexpression through dispatcher
 *
 * ## C++ dynamic_cast<>() Operator
 *
 * The dynamic_cast operator performs safe runtime type casting with three forms:
 * - **Downcast**: Cast from base to derived class (runtime check required)
 * - **Crosscast**: Cast across class hierarchy with multiple inheritance
 * - **Upcast**: Cast from derived to base (compile-time safe, but translated for consistency)
 *
 * Returns nullptr (for pointers) if cast fails at runtime.
 *
 * This handler detects CXXDynamicCastExpr nodes and delegates translation to DynamicCastTranslator.
 *
 * ## Integration with DynamicCastTranslator
 *
 * This handler is the dispatcher-side integration point for DynamicCastTranslator.
 * Flow:
 * 1. Dispatcher detects CXXDynamicCastExpr
 * 2. Handler extracts subexpression (pointer/reference being cast)
 * 3. Handler recursively dispatches subexpression
 * 4. Handler delegates to DynamicCastTranslator::translateDynamicCast()
 * 5. DynamicCastTranslator returns C code string
 * 6. Handler creates C expression from string
 * 7. Handler stores result in ExprMapper
 *
 * ## Translation Patterns
 *
 * **Downcast (base → derived)**:
 * ```cpp
 * // C++ Code:
 * Base* b = new Derived();
 * Derived* d = dynamic_cast<Derived*>(b);
 *
 * // Translated C:
 * struct Base* b = Derived_new();
 * struct Derived* d = (struct Derived*)cxx_dynamic_cast(
 *     b,
 *     &__ti_Base,     // Source type_info
 *     &__ti_Derived,  // Target type_info
 *     -1              // Runtime check required
 * );
 * ```
 *
 * **Crosscast (multiple inheritance)**:
 * ```cpp
 * // C++ Code (C : public A, public B):
 * C* c = new C();
 * B* b = dynamic_cast<B*>((A*)c);
 *
 * // Translated C:
 * struct C* c = C_new();
 * struct B* b = (struct B*)cxx_dynamic_cast(
 *     (struct A*)c,
 *     &__ti_A,
 *     &__ti_B,
 *     offsetof(struct C, B_base)  // Offset to B subobject
 * );
 * ```
 *
 * **Upcast (derived → base)**:
 * ```cpp
 * // C++ Code:
 * Derived* d = new Derived();
 * Base* b = dynamic_cast<Base*>(d);
 *
 * // Translated C:
 * struct Derived* d = Derived_new();
 * struct Base* b = (struct Base*)cxx_dynamic_cast(
 *     d,
 *     &__ti_Derived,
 *     &__ti_Base,
 *     0  // No offset for upcast
 * );
 * ```
 *
 * ## Runtime Function
 *
 * From transpiled/runtime/rtti_runtime.h:
 * ```c
 * void* cxx_dynamic_cast(const void* ptr,
 *                        const struct __class_type_info* src_type,
 *                        const struct __class_type_info* dst_type,
 *                        ptrdiff_t offset);
 * ```
 *
 * ## WHY This Matters
 *
 * RTTI via dynamic_cast is fundamental for:
 * - Safe type conversions: Detect incompatible casts at runtime
 * - Polymorphic dispatch: Cast to correct derived type
 * - Multiple inheritance: Navigate complex hierarchies
 * - Null-safe operations: Check cast success before use
 *
 * Without this handler, C++ code using dynamic_cast cannot transpile correctly.
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXDynamicCastExprHandler
 * @brief Translates C++ dynamic_cast<>() operator (CXXDynamicCastExpr) to C runtime cxx_dynamic_cast() calls
 *
 * Handles all dynamic_cast forms by delegating to DynamicCastTranslator.
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Detect CXXDynamicCastExpr
 * 2. Extract subexpression (pointer/reference being cast)
 * 3. Dispatch subexpression recursively via dispatcher
 * 4. Delegate to DynamicCastTranslator::translateDynamicCast()
 * 5. Create C expression from translation result
 * 6. Store C expression in ExprMapper
 *
 * Translation decisions:
 * - Downcast: Requires runtime type check (offset = -1)
 *   * Subexpression must be dispatched
 *   * Result is runtime call: `cxx_dynamic_cast(ptr, &__ti_Base, &__ti_Derived, -1)`
 * - Crosscast: Requires runtime check with offset calculation
 *   * Handles multiple inheritance
 *   * Result includes subobject offset
 * - Upcast: Compile-time safe but translated for consistency
 *   * Offset = 0 for direct upcast
 *
 * Cast failure handling:
 * - Pointer casts: Return NULL on failure
 * - Reference casts: NOT SUPPORTED in C (C has no exceptions)
 */
class CXXDynamicCastExprHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a CXXDynamicCastExpr
     * @param E Expression to check
     * @return true if E is CXXDynamicCastExpr, false otherwise
     *
     * Uses exact type matching with getStmtClass() for correctness.
     * Rejects CXXStaticCastExpr, CXXReinterpretCastExpr, CallExpr, etc.
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle CXXDynamicCastExpr translation with DynamicCastTranslator integration
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E CXXDynamicCastExpr to translate
     *
     * Flow:
     * 1. Cast E to CXXDynamicCastExpr
     * 2. Check ExprMapper for existing translation (prevent duplication)
     * 3. Extract subexpression (pointer/reference being cast)
     * 4. Recursively dispatch subexpression
     * 5. Delegate to DynamicCastTranslator::translateDynamicCast()
     * 6. Create C expression from translation result
     * 7. Store C expression in ExprMapper
     *
     * Logs detailed debug information for troubleshooting.
     */
    static void handleDynamicCast(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );

private:
    /**
     * @brief Dispatch subexpression recursively
     * @param disp Dispatcher for recursive dispatch
     * @param cppASTContext C++ ASTContext
     * @param cASTContext C ASTContext
     * @param castExpr CXXDynamicCastExpr with subexpression to dispatch
     *
     * Used for all dynamic_cast forms to ensure subexpression is translated.
     * Dispatches the subexpression (the pointer/reference being cast).
     */
    static void dispatchSubexpression(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::CXXDynamicCastExpr* castExpr
    );

    /**
     * @brief Create C expression from DynamicCastTranslator result
     * @param cASTContext Target C ASTContext
     * @param translationStr C code string from DynamicCastTranslator
     * @param resultType Type of the result expression
     * @return C expression representing the translation
     *
     * NOTE: Current implementation creates a StringLiteral as placeholder.
     * Future enhancement: Parse translationStr and create proper CallExpr
     * with cxx_dynamic_cast function call and proper arguments.
     */
    static clang::Expr* createCExprFromString(
        clang::ASTContext& cASTContext,
        const std::string& translationStr,
        clang::QualType resultType,
        clang::SourceLocation targetLoc
    );
};

} // namespace cpptoc
