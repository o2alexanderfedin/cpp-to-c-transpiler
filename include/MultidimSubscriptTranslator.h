/**
 * @file MultidimSubscriptTranslator.h
 * @brief Phase 1: Multidimensional Subscript Operator Support (C++23 P2128)
 *
 * Translates C++23 multidimensional subscript operators (`operator[](T1, T2, ...)`)
 * to equivalent C function calls. This enables support for matrix/tensor indexing
 * in the C++ to C transpiler.
 *
 * ## C++23 Feature: Multidimensional Subscript Operator
 *
 * C++23 introduced the ability to overload `operator[]` with multiple arguments,
 * allowing intuitive syntax for multidimensional data structures:
 *
 * ```cpp
 * class Matrix {
 * public:
 *     int& operator[](int row, int col);  // C++23
 *     const int& operator[](int row, int col) const;
 * };
 *
 * Matrix m;
 * m[i, j] = 42;  // Natural 2D indexing
 * int val = m[i, j];
 * ```
 *
 * Before C++23, workarounds were needed:
 * - `m[i][j]` (chained single subscripts, requires proxy objects)
 * - `m.at(i, j)` (explicit function call)
 * - `m(i, j)` (operator() overload)
 *
 * ## Translation Strategy
 *
 * The translator transforms multidimensional subscript operations into C function calls:
 *
 * ### Lvalue Context (Assignment Target)
 * ```cpp
 * m[i, j] = 42;
 * ```
 * Becomes:
 * ```c
 * *Matrix__subscript_2d(&m, i, j) = 42;
 * ```
 * Function returns pointer to allow assignment.
 *
 * ### Rvalue Context (Value Usage)
 * ```cpp
 * int val = m[i, j];
 * ```
 * Becomes:
 * ```c
 * int val = Matrix__subscript_2d_const(&m, i, j);
 * ```
 * Function returns value directly (const-qualified method).
 *
 * ## Implementation Architecture
 *
 * Follows the standard transpiler pattern (see VtableGenerator, TemplateExtractor):
 * 1. **Detection**: VisitCXXOperatorCallExpr identifies `operator[]` with 2+ arguments
 * 2. **Transformation**: transform() generates equivalent C function call
 * 3. **Function Generation**: Creates C function declarations for subscript operators
 * 4. **AST Replacement**: Replaces C++ operator call with C CallExpr
 *
 * ## Design Principles
 *
 * - **SOLID**: Single Responsibility (only handles subscript translation)
 * - **KISS**: Simple transformation logic (detect, generate, replace)
 * - **DRY**: Reuses CNodeBuilder for C AST construction
 * - **YAGNI**: Only supports what Phase 33 tests require
 *
 * ## Example Transformations
 *
 * ### 2D Matrix
 * ```cpp
 * class Matrix {
 *     int& operator[](int i, int j);
 * };
 * m[i, j] = 5;
 * ```
 * →
 * ```c
 * int* Matrix__subscript_2d(struct Matrix* self, int i, int j);
 * *Matrix__subscript_2d(&m, i, j) = 5;
 * ```
 *
 * ### 3D Tensor (Const)
 * ```cpp
 * class Tensor {
 *     float operator[](int x, int y, int z) const;
 * };
 * float v = t[x, y, z];
 * ```
 * →
 * ```c
 * float Tensor__subscript_3d_const(const struct Tensor* self, int x, int y, int z);
 * float v = Tensor__subscript_3d_const(&t, x, y, z);
 * ```
 *
 * ## References
 * - C++23 P2128: Multidimensional subscript operator
 * - Phase 1 Implementation Plan: .planning/phases/01-multidim-subscript/
 * - Phase 33 Tests: tests/real-world/cpp23-validation/gcc-adapted/multidim-subscript-P2128/
 *
 * @see CppToCVisitor::VisitCXXOperatorCallExpr for integration point
 * @see CNodeBuilder for C AST construction helpers
 */

#ifndef MULTIDIM_SUBSCRIPT_TRANSLATOR_H
#define MULTIDIM_SUBSCRIPT_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "CNodeBuilder.h"
#include <string>

/**
 * @class MultidimSubscriptTranslator
 * @brief Translates C++23 multidimensional subscript operators to C function calls
 *
 * This class handles the transformation of `operator[](T1, T2, ...)` calls into
 * equivalent C function calls, supporting both lvalue (assignment) and rvalue
 * (value usage) contexts.
 *
 * ## Thread Safety
 * - No shared mutable state (safe for parallel translation units)
 * - CNodeBuilder owns AST node creation (thread-local ASTContext)
 *
 * ## Performance Characteristics
 * - Detection: O(1) per operator call expression
 * - Transformation: O(n) where n = number of arguments
 * - Memory: <1KB per translation
 */
class MultidimSubscriptTranslator {
public:
    /**
     * @brief Construct translator with C AST builder
     * @param Builder CNodeBuilder for creating C AST nodes
     *
     * The Builder provides access to the ASTContext and helper methods
     * for constructing C declarations and expressions.
     */
    explicit MultidimSubscriptTranslator(clang::CNodeBuilder& Builder);

    /**
     * @brief Transform multidimensional subscript operator to C function call
     * @param E CXXOperatorCallExpr representing `obj[idx1, idx2, ...]`
     * @param Ctx Clang AST context
     * @param C_TU C translation unit for generated declarations
     * @return CallExpr for equivalent C function call, or nullptr if not multidimensional
     *
     * This is the main entry point called by CppToCVisitor when it encounters
     * a subscript operator call. It performs the following steps:
     *
     * 1. Validate that this is a multidimensional subscript (2+ indices)
     * 2. Determine context (lvalue vs rvalue) and const-qualification
     * 3. Generate or retrieve the C function declaration
     * 4. Build a CallExpr with:
     *    - Object address as first argument (`&obj`)
     *    - Index arguments following
     * 5. Wrap in dereference operator if lvalue context
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * m[i, j] = 42;  // CXXOperatorCallExpr(op=[], args=[m, i, j])
     *
     * // Output C AST
     * *Matrix__subscript_2d(&m, i, j) = 42;  // UnaryOp(*, CallExpr(...))
     * ```
     *
     * @note Returns nullptr for single-argument subscripts (handled by normal array indexing)
     */
    clang::CallExpr* transform(clang::CXXOperatorCallExpr* E,
                               clang::ASTContext& Ctx,
                               clang::TranslationUnitDecl* C_TU);

private:
    clang::CNodeBuilder& m_builder;

    /**
     * @brief Generate function name for multidimensional subscript
     * @param Class Class containing the operator
     * @param NumIndices Number of indices (2 for 2D, 3 for 3D, etc.)
     * @param IsConst Whether the operator is const-qualified
     * @return Function name (e.g., "Matrix__subscript_2d", "Tensor__subscript_3d_const")
     *
     * Naming convention:
     * - Non-const: `{ClassName}__subscript_{n}d`
     * - Const: `{ClassName}__subscript_{n}d_const`
     *
     * Examples:
     * - `Matrix__subscript_2d` for `int& operator[](int, int)`
     * - `Matrix__subscript_2d_const` for `const int& operator[](int, int) const`
     */
    std::string generateFunctionName(const clang::CXXRecordDecl* Class,
                                     unsigned NumIndices,
                                     bool IsConst);

    /**
     * @brief Get or create C function declaration for subscript operator
     * @param E The operator call expression
     * @param Ctx AST context
     * @param C_TU C translation unit to add declaration to
     * @return FunctionDecl for the C subscript function
     *
     * This method implements a "get-or-create" pattern:
     * - Checks if function already exists in C_TU
     * - If exists, returns existing declaration
     * - If not, creates new FunctionDecl with signature:
     *   ```c
     *   ReturnType* ClassName__subscript_Nd(struct ClassName* self, Type1 idx1, Type2 idx2, ...);
     *   ```
     *
     * For const operators, generates:
     * ```c
     * ReturnType ClassName__subscript_Nd_const(const struct ClassName* self, Type1 idx1, ...);
     * ```
     *
     * @note Function signature matches the C++ operator signature exactly
     */
    clang::FunctionDecl* getOrCreateSubscriptFunction(
        const clang::CXXOperatorCallExpr* E,
        clang::ASTContext& Ctx,
        clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Determine if expression is used in lvalue context
     * @param E Expression to check
     * @return true if expression appears on left side of assignment or similar
     *
     * Lvalue contexts include:
     * - Left side of assignment: `m[i,j] = 5`
     * - Passed to non-const reference: `foo(m[i,j])`
     * - Address taken: `&m[i,j]`
     *
     * Rvalue contexts include:
     * - Right side of assignment: `x = m[i,j]`
     * - Passed to value parameter: `bar(m[i,j])`
     * - Used in expression: `m[i,j] + 1`
     *
     * This determines whether to:
     * - Return pointer (lvalue): `*Matrix__subscript_2d(&m, i, j) = 5`
     * - Return value (rvalue): `x = Matrix__subscript_2d_const(&m, i, j)`
     *
     * @note Currently uses heuristic based on const-qualification of operator
     * @todo Phase 2: Implement proper parent expression analysis for context detection
     */
    bool isLValueContext(const clang::Expr* E);

    /**
     * @brief Get C type string from Clang QualType
     * @param Type Clang type to convert
     * @return C type string (e.g., "int", "struct Matrix", "float*")
     *
     * Helper method for generating function signatures.
     * Handles:
     * - Built-in types: int, float, double, etc.
     * - Class types: struct ClassName
     * - Pointer types: Type*
     * - Const qualification: const Type
     * - Reference types: stripped (C has no references)
     */
    std::string getTypeString(clang::QualType Type);
};

#endif // MULTIDIM_SUBSCRIPT_TRANSLATOR_H
