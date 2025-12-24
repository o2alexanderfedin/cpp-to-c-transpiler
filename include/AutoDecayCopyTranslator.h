/**
 * @file AutoDecayCopyTranslator.h
 * @brief Phase 6: auto(x) and auto{x} Decay-Copy Support (C++23 P0849R8)
 *
 * Translates C++23 auto(x) and auto{x} decay-copy expressions to explicit C copy
 * operations with type decay. This feature enables explicit decay operations for
 * references, arrays, and functions.
 *
 * ## C++23 Feature: auto(x) Decay-Copy (P0849R8)
 *
 * C++23 introduces auto(x) and auto{x} as explicit decay-copy expressions that
 * create copies of values with type decay rules applied:
 *
 * ```cpp
 * // Reference decay
 * int& ref = get_reference();
 * auto val = auto(ref);  // Creates copy, removes reference
 *
 * // Array decay
 * int arr[10];
 * auto ptr = auto(arr);  // Decays array to pointer
 *
 * // Const decay
 * const int& cref = 42;
 * auto copy = auto(cref);  // Removes const, creates copy
 *
 * // Function decay
 * void func();
 * auto fptr = auto(func);  // Decays to function pointer
 * ```
 *
 * ## Decay Rules
 *
 * | Source Type      | Decayed Type   | C Translation        |
 * |------------------|----------------|----------------------|
 * | `int&`           | `int`          | Dereference: `*ref`  |
 * | `const int&`     | `int`          | Copy, remove const   |
 * | `int[10]`        | `int*`         | Array decay (auto)   |
 * | `void()`         | `void(*)()`    | Function ptr: `&func`|
 * | `int`            | `int`          | Identity (value)     |
 *
 * ## Translation Strategy
 *
 * ### Reference → Value
 * ```cpp
 * int& ref = x;
 * auto val = auto(ref);
 * ```
 * Becomes:
 * ```c
 * int* ref = &x;
 * int val = *ref;  // Dereference to create copy
 * ```
 *
 * ### Array → Pointer
 * ```cpp
 * int arr[10];
 * auto ptr = auto(arr);
 * ```
 * Becomes:
 * ```c
 * int arr[10];
 * int* ptr = arr;  // Natural array decay in C
 * ```
 *
 * ### Function → Function Pointer
 * ```cpp
 * void func();
 * auto fptr = auto(func);
 * ```
 * Becomes:
 * ```c
 * void func();
 * void (*fptr)() = &func;  // Address-of operator
 * ```
 *
 * ## Implementation Architecture
 *
 * Follows the proven translator pattern:
 * 1. **Detection**: Check CXXFunctionalCastExpr with AutoType
 * 2. **Type Analysis**: Compute decayed type from source type
 * 3. **Copy Generation**: Create appropriate C expression based on decay rules
 * 4. **AST Replacement**: Replace auto(x) with C expression
 *
 * ## Design Principles
 *
 * - **SOLID**: Single Responsibility (only handles auto(x) decay-copy)
 * - **KISS**: Straightforward type decay algorithm
 * - **DRY**: Reuses CNodeBuilder for C AST construction
 * - **YAGNI**: Implements core decay rules, documents limitations
 *
 * ## Limitations
 *
 * - No support for class-type copy constructors (requires runtime library)
 * - auto{x} treated identically to auto(x) (direct-initialization vs copy)
 * - Template parameter decay not fully supported
 *
 * ## References
 * - C++23 P0849R8: auto(x) and auto{x}
 * - Phase 6 Implementation Plan: .planning/phases/06-auto-decay-copy/
 * - Phase 33 Tests: tests/real-world/cpp23-validation/gcc-adapted/auto-decay-P0849/
 *
 * @see CppToCVisitor::VisitCXXFunctionalCastExpr for detection
 */

#ifndef AUTO_DECAY_COPY_TRANSLATOR_H
#define AUTO_DECAY_COPY_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "CNodeBuilder.h"

/**
 * @class AutoDecayCopyTranslator
 * @brief Translates C++23 auto(x) decay-copy expressions to C
 *
 * This class handles the transformation of auto(x) and auto{x} expressions
 * into equivalent C code with explicit type decay and copy operations.
 *
 * ## Thread Safety
 * - No shared mutable state (safe for parallel translation units)
 * - CNodeBuilder owns AST node creation (thread-local ASTContext)
 *
 * ## Performance Characteristics
 * - Detection: O(1) per functional cast expression
 * - Type decay: O(1) type analysis
 * - Copy generation: O(1) expression creation
 */
class AutoDecayCopyTranslator {
public:
    /**
     * @brief Construct translator with C AST builder
     * @param Builder CNodeBuilder for creating C AST nodes
     */
    explicit AutoDecayCopyTranslator(clang::CNodeBuilder& Builder);

    /**
     * @brief Transform auto(x) or auto{x} expression to C
     * @param E CXXFunctionalCastExpr representing auto(x) or auto{x}
     * @param Ctx Clang AST context
     * @return Transformed expression (copy with decayed type), or nullptr if not auto(x)
     *
     * This method is called when CppToCVisitor encounters a functional cast
     * expression with AutoType. It analyzes the source expression type,
     * applies decay rules, and generates appropriate C copy expression.
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * int& ref = x;
     * auto(ref);  // CXXFunctionalCastExpr with AutoType
     *
     * // Output C AST
     * *ref;  // UnaryOperator (dereference) creating copy
     * ```
     *
     * @note Returns nullptr if expression is not auto(x) or auto{x}
     */
    clang::Expr* transform(clang::CXXFunctionalCastExpr* E,
                          clang::ASTContext& Ctx);

private:
    clang::CNodeBuilder& m_builder;

    /**
     * @brief Compute decayed type from source type
     * @param Ty Source type (may have references, arrays, functions)
     * @param Ctx AST context
     * @return Decayed type (removes references, decays arrays/functions)
     *
     * Applies standard C++ decay rules:
     * 1. Remove references (T& → T, T&& → T)
     * 2. Remove cv-qualifiers (const, volatile)
     * 3. Array-to-pointer decay (T[N] → T*)
     * 4. Function-to-pointer decay (T() → T(*)())
     *
     * Example transformations:
     * - const int& → int
     * - int[10] → int*
     * - void() → void(*)()
     * - int → int (identity)
     */
    clang::QualType computeDecayedType(clang::QualType Ty,
                                      clang::ASTContext& Ctx);

    /**
     * @brief Generate C copy expression for source with target type
     * @param Source Source expression to copy
     * @param DecayedType Target type after decay
     * @param Ctx AST context
     * @return C expression performing copy with decay
     *
     * Generates appropriate C expression based on source type:
     * - Reference: Dereference to create copy (*ref)
     * - Array: Identity (natural decay in C)
     * - Function: Address-of (&func)
     * - Value: Identity (already value type)
     *
     * Example:
     * ```c
     * // Reference → Value
     * int& ref = x;
     * auto val = auto(ref);  → int val = *ref;
     *
     * // Array → Pointer
     * int arr[10];
     * auto ptr = auto(arr);  → int* ptr = arr;
     * ```
     */
    clang::Expr* generateCopyExpression(clang::Expr* Source,
                                       clang::QualType DecayedType,
                                       clang::ASTContext& Ctx);

    /**
     * @brief Check if type is auto (placeholder type)
     * @param Ty Type to check
     * @return true if type contains AutoType
     *
     * Helper to detect auto(x) and auto{x} expressions by checking
     * if the cast target type is an auto placeholder.
     */
    bool isAutoType(clang::QualType Ty);
};

#endif // AUTO_DECAY_COPY_TRANSLATOR_H
