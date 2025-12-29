/**
 * @file StmtMapper.h
 * @brief Maps C++ source statements to created C target statements
 *
 * Single Responsibility: Manage C++ → C statement mappings for the transpiler.
 *
 * This class enables the Chain of Responsibility pattern by allowing:
 * - StatementHandler to store created C statements
 * - Other handlers to retrieve C statements created by StatementHandler
 *
 * Example:
 * - CompoundStmtHandler creates C CompoundStmt and stores: stmtMapper.setCreatedStmt(cppCompound, cCompound)
 * - FunctionHandler retrieves: cCompound = stmtMapper.getCreatedStmt(cppCompound)
 *
 * Design Principles:
 * - Single Responsibility: Only manages statement mappings
 * - Separation from DeclMapper: DeclMapper maps declarations, StmtMapper maps statements
 * - Separation from ExprMapper: ExprMapper maps expressions, StmtMapper maps statements
 */

#pragma once

#include "clang/AST/Stmt.h"
#include <map>

namespace cpptoc {

/**
 * @class StmtMapper
 * @brief Manages mappings from C++ statements to created C statements
 *
 * Responsibilities:
 * - Store C++ → C statement mappings
 * - Retrieve C statements for given C++ statements
 * - Support Chain of Responsibility pattern for handlers
 */
class StmtMapper {
public:
    /**
     * @brief Default constructor
     */
    StmtMapper() = default;

    /**
     * @brief Store mapping from C++ statement to created C statement
     * @param cppStmt Source C++ statement
     * @param cStmt Created C statement
     *
     * Enables handlers to retrieve statements created by statement handlers.
     *
     * Example:
     * ```cpp
     * // CompoundStmtHandler creates C compound statement and stores mapping
     * clang::CompoundStmt* cCompound = createCompoundStmt(...);
     * stmtMapper.setCreatedStmt(cppCompound, cCompound);
     *
     * // FunctionHandler retrieves created statement
     * clang::Stmt* cStmt = stmtMapper.getCreatedStmt(cppCompound);
     * ```
     */
    void setCreatedStmt(const clang::Stmt* cppStmt, clang::Stmt* cStmt);

    /**
     * @brief Get C statement created for a C++ statement
     * @param cppStmt Source C++ statement
     * @return Created C statement, or nullptr if not found
     *
     * Retrieves C statement previously stored via setCreatedStmt().
     * Returns nullptr if no mapping exists for the given C++ statement.
     */
    clang::Stmt* getCreatedStmt(const clang::Stmt* cppStmt) const;

    /**
     * @brief Check if a C++ statement has a mapped C statement
     * @param cppStmt Source C++ statement
     * @return true if mapping exists, false otherwise
     */
    bool hasCreatedStmt(const clang::Stmt* cppStmt) const;

private:
    std::map<const clang::Stmt*, clang::Stmt*> cppToCStmtMap_;
    ///< Maps C++ source statements to created C statements
    ///< Example: C++ CompoundStmt → C CompoundStmt, C++ ReturnStmt → C ReturnStmt
};

} // namespace cpptoc
