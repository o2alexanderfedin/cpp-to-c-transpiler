/**
 * @file StaticOperatorTranslator.h
 * @brief Phase 2: Static operator() and operator[] Support (C++23 P1169R4)
 *
 * Translates C++23 static operator() and operator[] calls to equivalent C
 * function calls. This enables support for static callable objects and static
 * subscript operators in the C++ to C transpiler.
 *
 * ## C++23 Feature: Static operator() and operator[]
 *
 * C++23 allows operator() and operator[] to be declared static, meaning they
 * don't have access to `this` and operate purely on their arguments:
 *
 * ```cpp
 * struct Calculator {
 *     static int operator()(int a, int b) { return a + b; }
 * };
 *
 * struct LookupTable {
 *     static int operator[](int key) { return table[key]; }
 * };
 *
 * int result = Calculator{}(1, 2);  // or Calculator::operator()(1, 2)
 * int value = LookupTable{}[42];
 * ```
 *
 * ## Translation Strategy
 *
 * Since static operators have no implicit `this` parameter, translation is
 * simpler than instance operators:
 *
 * ### Static operator()
 * ```cpp
 * Calculator{}(1, 2);
 * ```
 * Becomes:
 * ```c
 * Calculator__call_static(1, 2);
 * ```
 *
 * ### Static operator[] (single arg)
 * ```cpp
 * LookupTable{}[key];
 * ```
 * Becomes:
 * ```c
 * LookupTable__subscript_static(key);
 * ```
 *
 * ### Static operator[] (multi-arg, combines with Phase 1)
 * ```cpp
 * Matrix::operator[](i, j);
 * ```
 * Becomes:
 * ```c
 * Matrix__subscript_2d_static(i, j);
 * ```
 *
 * ## Implementation Architecture
 *
 * Follows the proven translator pattern from Phase 1:
 * 1. **Detection**: VisitCXXMethodDecl identifies static operator() or operator[]
 * 2. **Function Generation**: Creates C function declaration without `this` parameter
 * 3. **Call Translation**: VisitCXXOperatorCallExpr transforms call sites
 * 4. **AST Replacement**: Replaces C++ operator call with C CallExpr
 *
 * ## Design Principles
 *
 * - **SOLID**: Single Responsibility (only handles static operators)
 * - **KISS**: Simpler than instance operators (no `this` parameter)
 * - **DRY**: Reuses CNodeBuilder for C AST construction
 * - **YAGNI**: Only supports what Phase 33 tests require
 *
 * ## Differences from Instance Operators
 *
 * | Feature | Instance | Static |
 * |---------|----------|--------|
 * | `this` parameter | Yes (first param) | No |
 * | Call syntax | `obj()` or `obj[]` | `Class{}()` or `Class::op()` |
 * | C function signature | `(struct Class* self, ...)` | `(...)` |
 *
 * ## References
 * - C++23 P1169R4: Static operator() and operator[]
 * - Phase 2 Implementation Plan: .planning/phases/02-static-operators/
 * - Phase 33 Tests: tests/real-world/cpp23-validation/gcc-adapted/static-operators-P1169/
 *
 * @see CppToCVisitor::VisitCXXMethodDecl for method detection
 * @see CppToCVisitor::VisitCXXOperatorCallExpr for call site transformation
 * @see MultidimSubscriptTranslator for instance operator[] support
 */

#ifndef STATIC_OPERATOR_TRANSLATOR_H
#define STATIC_OPERATOR_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "CNodeBuilder.h"
#include <string>

/**
 * @class StaticOperatorTranslator
 * @brief Translates C++23 static operator() and operator[] to C function calls
 *
 * This class handles the transformation of static operator calls into
 * equivalent C function calls. Unlike instance operators, static operators
 * don't require a `this` parameter, making translation more straightforward.
 *
 * ## Thread Safety
 * - No shared mutable state (safe for parallel translation units)
 * - CNodeBuilder owns AST node creation (thread-local ASTContext)
 *
 * ## Performance Characteristics
 * - Detection: O(1) per method declaration
 * - Transformation: O(n) where n = number of arguments
 * - Memory: <500 bytes per translation
 */
class StaticOperatorTranslator {
public:
    /**
     * @brief Construct translator with C AST builder
     * @param Builder CNodeBuilder for creating C AST nodes
     */
    explicit StaticOperatorTranslator(clang::CNodeBuilder& Builder);

    /**
     * @brief Transform static operator method to C function declaration
     * @param MD CXXMethodDecl representing static operator() or operator[]
     * @param Ctx Clang AST context
     * @param C_TU C translation unit for generated declarations
     * @return FunctionDecl for equivalent C function, or nullptr if not static operator
     *
     * This method is called when CppToCVisitor encounters a static operator
     * method declaration. It generates a C function with:
     * - No `this` parameter (key difference from instance operators)
     * - Same parameter list as C++ operator
     * - Same return type as C++ operator
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * struct Calculator {
     *     static int operator()(int a, int b);  // CXXMethodDecl
     * };
     *
     * // Output C AST
     * int Calculator__call_static(int a, int b);  // FunctionDecl
     * ```
     *
     * @note Returns nullptr if method is not a static operator
     */
    clang::FunctionDecl* transformMethod(clang::CXXMethodDecl* MD,
                                         clang::ASTContext& Ctx,
                                         clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Transform static operator call site to C function call
     * @param E CXXOperatorCallExpr representing call to static operator
     * @param Ctx Clang AST context
     * @return CallExpr for equivalent C function call, or nullptr if not static
     *
     * This method is called when CppToCVisitor encounters a static operator
     * call expression. It builds a CallExpr with:
     * - Reference to the generated static function
     * - Arguments from the call (skipping arg 0 which is the object)
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * Calculator{}(1, 2);  // CXXOperatorCallExpr(args=[Calculator{}, 1, 2])
     *
     * // Output C AST
     * Calculator__call_static(1, 2);  // CallExpr(args=[1, 2])
     * ```
     *
     * Key insight: In CXXOperatorCallExpr for static operators,
     * arg 0 is the object (e.g., `Calculator{}`), but it's unused
     * since the operator is static. We skip it in the C call.
     *
     * @note Returns nullptr if operator is not static
     */
    clang::CallExpr* transformCall(clang::CXXOperatorCallExpr* E,
                                   clang::ASTContext& Ctx);

private:
    clang::CNodeBuilder& m_builder;

    /**
     * @brief Generate function name for static operator
     * @param MD The static operator method declaration
     * @return Function name (e.g., "Calculator__call_static")
     *
     * Naming convention:
     * - operator(): `{ClassName}__call_static`
     * - operator[] (single arg): `{ClassName}__subscript_static`
     * - operator[] (multi-arg): `{ClassName}__subscript_{n}d_static`
     *
     * Examples:
     * - `Calculator__call_static` for `static int operator()(int, int)`
     * - `LookupTable__subscript_static` for `static int operator[](int)`
     * - `Matrix__subscript_2d_static` for `static int operator[](int, int)`
     */
    std::string generateStaticOperatorName(const clang::CXXMethodDecl* MD);

    /**
     * @brief Find or create C function for static operator
     * @param MD The C++ static operator method
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return FunctionDecl for the C function
     *
     * Implements "get-or-create" pattern:
     * - Checks if function already exists in C_TU
     * - If exists, returns existing declaration
     * - If not, creates new FunctionDecl with signature matching operator
     *
     * For static operators, signature is straightforward:
     * ```c
     * ReturnType ClassName__op_static(Type1 arg1, Type2 arg2, ...);
     * ```
     *
     * No `this` parameter is added (key difference from instance operators).
     */
    clang::FunctionDecl* findOrCreateStaticFunction(
        const clang::CXXMethodDecl* MD,
        clang::ASTContext& Ctx,
        clang::TranslationUnitDecl* C_TU);
};

#endif // STATIC_OPERATOR_TRANSLATOR_H
