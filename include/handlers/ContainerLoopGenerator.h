/**
 * @file ContainerLoopGenerator.h
 * @brief Generator for container-based range-for loop translation (Phase 54)
 *
 * Generates iterator-based C for loops for range-based for loops over custom containers.
 * Translates `for (T x : container)` to iterator-based loop with begin/end/operator++/operator*.
 *
 * Scope (Phase 54 - Task 3):
 * - Generate iterator-based for loop structure
 * - Create begin and end iterator variables
 * - Generate iterator comparison, increment, and dereference calls
 * - Support both by-value and by-reference semantics (future)
 *
 * Translation Pattern:
 *
 * **By-Value with Struct Iterator:**
 * ```cpp
 * // C++ Input
 * IntList list;
 * for (int x : list) {
 *     printf("%d\n", x);
 * }
 *
 * // C Output
 * struct IntList list;
 * {
 *     struct IntList_Iterator __begin = IntList__begin(&list);
 *     struct IntList_Iterator __end = IntList__end(&list);
 *     for (; IntList_Iterator__not_equal(&__begin, &__end);
 *          IntList_Iterator__increment(&__begin)) {
 *         int x = IntList_Iterator__deref(&__begin);
 *         printf("%d\n", x);
 *     }
 * }
 * ```
 *
 * **By-Value with Pointer Iterator:**
 * ```cpp
 * // C++ Input
 * for (int x : array_wrapper) {
 *     use(x);
 * }
 *
 * // C Output
 * {
 *     int* __begin = ArrayWrapper__begin(&array_wrapper);
 *     int* __end = ArrayWrapper__end(&array_wrapper);
 *     for (; __begin != __end; ++__begin) {
 *         int x = *__begin;
 *         use(x);
 *     }
 * }
 * ```
 */

#pragma once

#include "handlers/RangeTypeAnalyzer.h"
#include "handlers/LoopVariableAnalyzer.h"
#include "handlers/IteratorTypeAnalyzer.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ASTContext.h"
#include <string>

// Forward declaration (global namespace - matches actual definition)
class CppToCVisitorDispatcher;

namespace cpptoc {

/**
 * @class ContainerLoopGenerator
 * @brief Generates iterator-based for loops for custom container iteration
 *
 * Follows Single Responsibility Principle - only generates container loops,
 * does not handle arrays or STL containers.
 *
 * Note: This is a helper class used by StatementHandler, not a dispatcher handler itself.
 */
class ContainerLoopGenerator {
public:
    /**
     * @brief Constructor
     * @param disp Dispatcher for recursive AST node processing
     */
    explicit ContainerLoopGenerator(CppToCVisitorDispatcher& disp) : disp_(disp) {}

    /**
     * @brief Generate a for loop for custom container iteration
     * @param RFS Original C++ range-for statement
     * @param rangeInfo Classification of the range (must be CustomType)
     * @param loopVarInfo Information about the loop variable
     * @param cppASTContext C++ AST context (for reading C++ nodes)
     * @param cASTContext C AST context (for creating C nodes)
     * @return C ForStmt representing the iterator-based loop
     */
    clang::ForStmt* generate(
        const clang::CXXForRangeStmt* RFS,
        const RangeClassification& rangeInfo,
        const LoopVariableInfo& loopVarInfo,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );

private:
    /**
     * @brief Generate unique iterator variable names
     * @return Pair of begin and end variable names
     */
    std::pair<std::string, std::string> generateIteratorVarNames();

    /**
     * @brief Create begin iterator variable declaration
     * @param beginVarName Name of begin iterator variable
     * @param iteratorType Type of the iterator
     * @param containerExpr Expression for the container
     * @param containerType Type of the container
     * @param cASTContext C AST context for creating nodes
     * @return VarDecl for begin iterator with initialization
     */
    clang::VarDecl* createBeginIterator(
        const std::string& beginVarName,
        clang::QualType iteratorType,
        const clang::Expr* containerExpr,
        clang::QualType containerType,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create end iterator variable declaration
     * @param endVarName Name of end iterator variable
     * @param iteratorType Type of the iterator
     * @param containerExpr Expression for the container
     * @param containerType Type of the container
     * @param cASTContext C AST context for creating nodes
     * @return VarDecl for end iterator with initialization
     */
    clang::VarDecl* createEndIterator(
        const std::string& endVarName,
        clang::QualType iteratorType,
        const clang::Expr* containerExpr,
        clang::QualType containerType,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create iterator comparison condition (begin != end)
     * @param beginVar Begin iterator variable
     * @param endVar End iterator variable
     * @param iterClass Iterator classification
     * @param cASTContext C AST context for creating nodes
     * @return Condition expression
     */
    clang::Expr* createIteratorComparison(
        clang::VarDecl* beginVar,
        clang::VarDecl* endVar,
        const IteratorClassification& iterClass,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create iterator increment expression (++begin)
     * @param beginVar Begin iterator variable
     * @param iterClass Iterator classification
     * @param cASTContext C AST context for creating nodes
     * @return Increment expression
     */
    clang::Expr* createIteratorIncrement(
        clang::VarDecl* beginVar,
        const IteratorClassification& iterClass,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create loop body with element access
     * @param RFS Original range-for statement
     * @param beginVar Begin iterator variable
     * @param loopVarInfo Loop variable information
     * @param iterClass Iterator classification
     * @param cppASTContext C++ AST context (for reading C++ nodes)
     * @param cASTContext C AST context (for creating C nodes)
     * @return CompoundStmt containing variable declaration and original body
     */
    clang::CompoundStmt* createLoopBody(
        const clang::CXXForRangeStmt* RFS,
        clang::VarDecl* beginVar,
        const LoopVariableInfo& loopVarInfo,
        const IteratorClassification& iterClass,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create element access variable declaration
     * @param RFS Original range-for statement
     * @param beginVar Begin iterator variable
     * @param loopVarInfo Loop variable information
     * @param iterClass Iterator classification
     * @param cASTContext C AST context for creating nodes
     * @return DeclStmt for element variable (T x = *begin)
     */
    clang::DeclStmt* createElementVarDecl(
        const clang::CXXForRangeStmt* RFS,
        clang::VarDecl* beginVar,
        const LoopVariableInfo& loopVarInfo,
        const IteratorClassification& iterClass,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create iterator dereference expression (*begin)
     * @param beginVar Begin iterator variable
     * @param iterClass Iterator classification
     * @param cASTContext C AST context for creating nodes
     * @return Dereference expression
     */
    clang::Expr* createIteratorDereference(
        clang::VarDecl* beginVar,
        const IteratorClassification& iterClass,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create call to Container::begin() method
     * @param containerExpr Expression for the container
     * @param containerType Type of the container
     * @param cASTContext C AST context for creating nodes
     * @return CallExpr to begin() method
     */
    clang::Expr* createBeginCall(
        const clang::Expr* containerExpr,
        clang::QualType containerType,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create call to Container::end() method
     * @param containerExpr Expression for the container
     * @param containerType Type of the container
     * @param cASTContext C AST context for creating nodes
     * @return CallExpr to end() method
     */
    clang::Expr* createEndCall(
        const clang::Expr* containerExpr,
        clang::QualType containerType,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create compound statement with iterator declarations
     * @param beginDecl Begin iterator declaration
     * @param endDecl End iterator declaration
     * @param forLoop The for loop itself
     * @param cASTContext C AST context for creating nodes
     * @return CompoundStmt wrapping iterator declarations and loop
     */
    clang::CompoundStmt* createIteratorScope(
        clang::VarDecl* beginDecl,
        clang::VarDecl* endDecl,
        clang::ForStmt* forLoop,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Find begin() method in container type
     * @param containerType Type of the container
     * @return begin() method declaration, or nullptr if not found
     */
    const clang::CXXMethodDecl* findBeginMethod(
        clang::QualType containerType
    );

    /**
     * @brief Find end() method in container type
     * @param containerType Type of the container
     * @return end() method declaration, or nullptr if not found
     */
    const clang::CXXMethodDecl* findEndMethod(
        clang::QualType containerType
    );

    /// Dispatcher for recursive AST node processing
    CppToCVisitorDispatcher& disp_;

    /// Counter for generating unique iterator variable names
    static unsigned iteratorVarCounter_;
};

} // namespace cpptoc
