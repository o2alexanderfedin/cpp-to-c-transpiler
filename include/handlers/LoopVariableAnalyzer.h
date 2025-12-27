/**
 * @file LoopVariableAnalyzer.h
 * @brief Analyzer for range-for loop variable declarations (Phase 54)
 *
 * Analyzes the loop variable in range-based for loops to determine:
 * - Variable name
 * - Variable type (explicit or auto-deduced)
 * - Value category (by-value, by-const-ref, by-mutable-ref)
 * - Structured binding detection (for pairs/tuples)
 *
 * Scope (Phase 54 - Task 3):
 * - Extract loop variable name and type
 * - Determine value category for efficient translation
 * - Detect structured bindings (basic support)
 *
 * Value Category Examples:
 * - for (int x : arr)          => By-value
 * - for (const int& x : arr)   => By-const-ref (efficient)
 * - for (int& x : arr)         => By-mutable-ref (modifiable)
 * - for (auto x : vec)         => By-value (auto)
 * - for (const auto& x : vec)  => By-const-ref (auto)
 * - for (auto [k, v] : map)    => Structured binding (deferred)
 */

#pragma once

#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include <string>
#include <vector>

namespace cpptoc {

/**
 * @enum ValueCategory
 * @brief How the loop variable is bound to the range element
 */
enum class ValueCategory {
    Unknown,        ///< Cannot determine
    ByValue,        ///< Copy each element (int x, auto x)
    ByConstRef,     ///< Const reference (const int& x, const auto& x)
    ByMutableRef,   ///< Mutable reference (int& x, auto& x)
    ByRValueRef     ///< Universal reference (auto&& x) - deferred to Phase 57
};

/**
 * @struct LoopVariableInfo
 * @brief Complete information about a range-for loop variable
 */
struct LoopVariableInfo {
    /// Variable name
    std::string name;

    /// Variable type (may be auto)
    clang::QualType type;

    /// Value category
    ValueCategory category = ValueCategory::Unknown;

    /// Is the type auto-deduced?
    bool isAuto = false;

    /// Is the type const-qualified?
    bool isConst = false;

    /// Is the type a reference?
    bool isReference = false;

    /// Is this a structured binding? (e.g., auto [k, v])
    bool isStructuredBinding = false;

    /// For structured bindings: variable names
    std::vector<std::string> bindingNames;

    /// The VarDecl from the AST
    const clang::VarDecl* varDecl = nullptr;

    /// Is this valid and translatable?
    bool isValid() const {
        return !name.empty() && varDecl != nullptr;
    }
};

/**
 * @class LoopVariableAnalyzer
 * @brief Analyzes loop variables in range-for loops
 *
 * Follows Single Responsibility Principle - only analyzes loop variables,
 * does not perform translation.
 */
class LoopVariableAnalyzer {
public:
    /**
     * @brief Analyze the loop variable in a range-for loop
     * @param RFS C++ CXXForRangeStmt
     * @return Loop variable information
     */
    LoopVariableInfo analyze(const clang::CXXForRangeStmt* RFS);

    /**
     * @brief Extract loop variable declaration from range-for loop
     * @param RFS C++ CXXForRangeStmt
     * @return Loop variable VarDecl, or nullptr if not found
     */
    static const clang::VarDecl* getLoopVariable(const clang::CXXForRangeStmt* RFS);

private:
    /**
     * @brief Determine value category from variable type
     * @param type Variable type
     * @return Value category
     */
    ValueCategory determineValueCategory(clang::QualType type);

    /**
     * @brief Check if type is auto-deduced
     * @param type Variable type
     * @return true if type uses auto
     */
    bool isAutoType(clang::QualType type);

    /**
     * @brief Check if variable is a structured binding
     * @param VD Variable declaration
     * @return true if structured binding
     */
    bool isStructuredBinding(const clang::VarDecl* VD);

    /**
     * @brief Extract binding names from structured binding
     * @param VD Variable declaration
     * @return Vector of binding names
     */
    std::vector<std::string> extractBindingNames(const clang::VarDecl* VD);
};

} // namespace cpptoc
