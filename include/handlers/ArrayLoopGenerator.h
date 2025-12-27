/**
 * @file ArrayLoopGenerator.h
 * @brief Generator for array-based range-for loop translation (Phase 54)
 *
 * Generates traditional C for loops for range-based for loops over C arrays.
 * Translates `for (T x : arr)` to `for (size_t i = 0; i < N; ++i) { T x = arr[i]; }`
 *
 * Scope (Phase 54 - Task 4):
 * - Generate index-based for loop structure
 * - Create unique index variable names
 * - Handle array element access
 * - Support both by-value and by-reference semantics
 *
 * Translation Pattern:
 *
 * **By-Value:**
 * ```cpp
 * // C++
 * int arr[5] = {1, 2, 3, 4, 5};
 * for (int x : arr) {
 *     printf("%d\n", x);
 * }
 *
 * // C
 * int arr[5] = {1, 2, 3, 4, 5};
 * for (size_t __range_i_0 = 0; __range_i_0 < 5; ++__range_i_0) {
 *     int x = arr[__range_i_0];
 *     printf("%d\n", x);
 * }
 * ```
 *
 * **By-Reference:**
 * ```cpp
 * // C++
 * for (int& x : arr) {
 *     x *= 2;
 * }
 *
 * // C
 * for (size_t __range_i_0 = 0; __range_i_0 < 5; ++__range_i_0) {
 *     int* x = &arr[__range_i_0];
 *     *x *= 2;
 * }
 * ```
 */

#pragma once

#include "handlers/RangeTypeAnalyzer.h"
#include "handlers/LoopVariableAnalyzer.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/Stmt.h"
#include <string>

namespace cpptoc {

/**
 * @class ArrayLoopGenerator
 * @brief Generates index-based for loops for C array iteration
 *
 * Follows Single Responsibility Principle - only generates array loops,
 * does not handle containers or custom types.
 */
class ArrayLoopGenerator {
public:
    /**
     * @brief Constructor
     * @param ctx Handler context for AST node creation
     */
    explicit ArrayLoopGenerator(HandlerContext& ctx) : ctx_(ctx) {}

    /**
     * @brief Generate a for loop for C array iteration
     * @param RFS Original C++ range-for statement
     * @param rangeInfo Classification of the range
     * @param loopVarInfo Information about the loop variable
     * @return C ForStmt representing the index-based loop
     */
    clang::ForStmt* generate(
        const clang::CXXForRangeStmt* RFS,
        const RangeClassification& rangeInfo,
        const LoopVariableInfo& loopVarInfo
    );

private:
    /**
     * @brief Generate unique index variable name
     * @return Index variable name (e.g., "__range_i_0", "__range_i_1")
     */
    std::string generateIndexVarName();

    /**
     * @brief Create index variable declaration
     * @param indexVarName Name of index variable
     * @return VarDecl for index variable (size_t idx = 0)
     */
    clang::VarDecl* createIndexVarDecl(const std::string& indexVarName);

    /**
     * @brief Create loop condition (idx < arraySize)
     * @param indexVar Index variable declaration
     * @param arraySize Array size
     * @return Condition expression
     */
    clang::Expr* createLoopCondition(
        clang::VarDecl* indexVar,
        uint64_t arraySize
    );

    /**
     * @brief Create loop increment (++idx)
     * @param indexVar Index variable declaration
     * @return Increment expression
     */
    clang::Expr* createLoopIncrement(clang::VarDecl* indexVar);

    /**
     * @brief Create loop body with element access
     * @param RFS Original range-for statement
     * @param indexVar Index variable declaration
     * @param loopVarInfo Loop variable information
     * @return CompoundStmt containing variable declaration and original body
     */
    clang::CompoundStmt* createLoopBody(
        const clang::CXXForRangeStmt* RFS,
        clang::VarDecl* indexVar,
        const LoopVariableInfo& loopVarInfo
    );

    /**
     * @brief Create element access variable declaration
     * @param RFS Original range-for statement
     * @param indexVar Index variable declaration
     * @param loopVarInfo Loop variable information
     * @return DeclStmt for element variable (T x = arr[i] or T* x = &arr[i])
     */
    clang::DeclStmt* createElementVarDecl(
        const clang::CXXForRangeStmt* RFS,
        clang::VarDecl* indexVar,
        const LoopVariableInfo& loopVarInfo
    );

    /**
     * @brief Create array subscript expression (arr[i])
     * @param RFS Original range-for statement
     * @param indexVar Index variable declaration
     * @return ArraySubscriptExpr
     */
    clang::Expr* createArraySubscript(
        const clang::CXXForRangeStmt* RFS,
        clang::VarDecl* indexVar
    );

    /// Handler context for AST node creation
    HandlerContext& ctx_;

    /// Counter for generating unique index variable names
    static unsigned indexVarCounter_;
};

} // namespace cpptoc
