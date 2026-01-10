/**
 * @file StmtMapper.h
 * @brief RAII mapper for C++ statements to created C statements
 *
 * This provides a per-instance mapper around NodeMapper using RAII pattern.
 * Each instance maintains its own mapping state.
 *
 * Single Responsibility: Provide statement-specific mapper for NodeMapper.
 *
 * Usage:
 * - Create: StmtMapper stmtMapper;
 * - Usage: stmtMapper.setCreated(cppStmt, cStmt)
 * - Usage: stmtMapper.getCreated(cppStmt)
 * - Usage: stmtMapper.hasCreated(cppStmt)
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

/**
 * @class StmtMapper
 * @brief RAII wrapper for mapping C++ statements to created C statements
 *
 * Wraps NodeMapper<clang::Stmt, clang::Stmt*> with RAII semantics.
 * Each test/thread creates its own instance for complete isolation.
 *
 * Example:
 * ```cpp
 * auto stmtMapper = std::make_unique<StmtMapper>();
 * stmtMapper->setCreated(cppCompound, cCompound);
 * clang::Stmt* cStmt = stmtMapper->getCreated(cppCompound);
 * if (stmtMapper->hasCreated(cppCompound)) { ... }
 * ```
 */
class StmtMapper {
public:
  /**
   * @brief Public constructor for RAII pattern
   *
   * **RAII Pattern**: Each test creates its own StmtMapper instance
   * **Thread Safety**: Each thread/test has isolated instance - fully thread-safe
   */
  StmtMapper() = default;

  /**
   * @brief Store mapping from C++ statement to created C statement
   * @param cppNode Source C++ statement
   * @param cNode Created C statement
   */
  void setCreated(const clang::Stmt* cppNode, clang::Stmt* cNode) {
    mapper_.setCreated(cppNode, cNode);
  }

  /**
   * @brief Get C statement created for a C++ statement
   * @param cppNode Source C++ statement
   * @return Created C statement, or nullptr if not found
   */
  clang::Stmt* getCreated(const clang::Stmt* cppNode) const {
    return mapper_.getCreated(cppNode);
  }

  /**
   * @brief Check if a C++ statement has a mapped C statement
   * @param cppNode Source C++ statement
   * @return true if mapping exists, false otherwise
   */
  bool hasCreated(const clang::Stmt* cppNode) const {
    return mapper_.hasCreated(cppNode);
  }

  // Prevent copying (use move semantics or unique_ptr instead)
  StmtMapper(const StmtMapper&) = delete;
  StmtMapper& operator=(const StmtMapper&) = delete;

  // Allow move semantics for modern C++
  StmtMapper(StmtMapper&&) = default;
  StmtMapper& operator=(StmtMapper&&) = default;

private:
  NodeMapper<clang::Stmt, clang::Stmt*> mapper_;
};

} // namespace cpptoc
