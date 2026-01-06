/**
 * @file RangeTypeAnalyzer.h
 * @brief Analyzer for detecting and classifying range-for loop types (Phase 54)
 *
 * Analyzes C++ range-based for loops (CXXForRangeStmt) and classifies them
 * by range type to determine appropriate translation strategy.
 *
 * Scope (Phase 54 - Task 1):
 * - Detect CXXForRangeStmt nodes
 * - Classify range type (C array, STL container, custom type)
 * - Determine if range provides begin/end methods or free functions
 * - Extract array size for C arrays
 *
 * Classification Strategy:
 * 1. **C Array**: ConstantArrayType with compile-time size
 *    Translation: Index-based for loop
 * 2. **STL Container**: std::vector, std::array, std::map, etc.
 *    Translation: Iterator-based loop with begin/end
 * 3. **Custom Type**: User-defined type with begin/end
 *    Translation: Iterator-based loop with begin/end
 *
 * Example Classifications:
 * - int arr[5]        => RangeType::CArray, size=5
 * - std::vector<int>  => RangeType::STLContainer (vector)
 * - std::map<K,V>     => RangeType::STLContainer (map)
 * - CustomContainer   => RangeType::CustomType
 */

#pragma once

#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/Type.h"
#include <optional>
#include <string>

namespace cpptoc {

/**
 * @enum RangeType
 * @brief Classification of range types for range-for loops
 */
enum class RangeType {
    Unknown,        ///< Cannot determine range type
    CArray,         ///< C array with compile-time size
    STLContainer,   ///< STL container (vector, map, array, etc.)
    CustomType      ///< User-defined type with begin/end
};

/**
 * @enum BeginEndKind
 * @brief How begin/end are provided for the range
 */
enum class BeginEndKind {
    Unknown,         ///< Cannot determine
    MemberFunction,  ///< container.begin() / container.end()
    FreeFunction,    ///< begin(container) / end(container)
    NotApplicable    ///< C array - doesn't use begin/end
};

/**
 * @struct RangeClassification
 * @brief Complete classification of a range-for loop's range
 */
struct RangeClassification {
    RangeType rangeType = RangeType::Unknown;
    BeginEndKind beginEndKind = BeginEndKind::Unknown;

    /// For C arrays: array size (compile-time constant)
    std::optional<uint64_t> arraySize;

    /// Container/type name (e.g., "vector", "map", "CustomContainer")
    std::string typeName;

    /// Element type of the range
    clang::QualType elementType;

    /// Is the range const-qualified?
    bool isConst = false;

    /// Is this a valid, translatable range?
    bool isValid() const {
        return rangeType != RangeType::Unknown;
    }
};

/**
 * @class RangeTypeAnalyzer
 * @brief Analyzes range-for loops and classifies range types
 *
 * Follows Single Responsibility Principle - only classifies ranges,
 * does not perform translation.
 */
class RangeTypeAnalyzer {
public:
    /**
     * @brief Analyze a range-for loop and classify its range
     * @param RFS C++ CXXForRangeStmt
     * @return Classification result
     */
    RangeClassification analyze(const clang::CXXForRangeStmt* RFS);

    /**
     * @brief Check if a statement is a range-for loop
     * @param S Statement to check
     * @return true if S is a CXXForRangeStmt
     */
    static bool isRangeForStmt(const clang::Stmt* S);

    /**
     * @brief Extract range expression from range-for loop
     * @param RFS C++ CXXForRangeStmt
     * @return Range expression, or nullptr if not found
     */
    static const clang::Expr* getRangeExpr(const clang::CXXForRangeStmt* RFS);

private:
    /**
     * @brief Classify the type of a range expression
     * @param rangeExpr Range expression
     * @return Range classification
     */
    RangeClassification classifyRangeType(const clang::Expr* rangeExpr);

    /**
     * @brief Check if type is a C array
     * @param type Type to check
     * @return Array size if C array, nullopt otherwise
     */
    std::optional<uint64_t> tryGetCArraySize(clang::QualType type);

    /**
     * @brief Check if type is an STL container
     * @param type Type to check
     * @return Container name if STL container, empty string otherwise
     */
    std::string tryGetSTLContainerName(clang::QualType type);

    /**
     * @brief Determine how begin/end are provided
     * @param type Container/range type
     * @return BeginEndKind
     */
    BeginEndKind determineBeginEndKind(clang::QualType type);

    /**
     * @brief Extract element type from range type
     * @param type Range type
     * @return Element type
     */
    clang::QualType extractElementType(clang::QualType type);
};

} // namespace cpptoc
