/**
 * @file StmtMapper.h
 * @brief Singleton wrapper for mapping C++ statements to created C statements
 *
 * This provides a singleton wrapper around NodeMapper to ensure all source files
 * share the same mapping instance during a transpilation session.
 *
 * Single Responsibility: Provide statement-specific singleton mapper for NodeMapper.
 *
 * Migration Note:
 * - Old: StmtMapper stmtMapper;
 * - New: StmtMapper& stmtMapper = StmtMapper::getInstance();
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
 * @brief Singleton wrapper for mapping C++ statements to created C statements
 *
 * Wraps NodeMapper<clang::Stmt, clang::Stmt*> in a singleton pattern to ensure
 * all source files share the same statement mappings during transpilation.
 *
 * Example:
 * ```cpp
 * StmtMapper& stmtMapper = StmtMapper::getInstance();
 * stmtMapper.setCreated(cppCompound, cCompound);
 * clang::Stmt* cStmt = stmtMapper.getCreated(cppCompound);
 * if (stmtMapper.hasCreated(cppCompound)) { ... }
 * ```
 */
class StmtMapper {
public:
  /**
   * @brief Get the singleton StmtMapper instance
   * @return Reference to the global StmtMapper instance
   *
   * **Singleton Pattern**: Ensures all files share the same StmtMapper
   * **Thread Safety**: Not thread-safe; call from single thread during transpilation
   */
  static StmtMapper& getInstance() {
    static StmtMapper instance;
    return instance;
  }

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

  /**
   * @brief Reset all mappings (for testing)
   */
  static void reset() {
    getInstance().mapper_ = NodeMapper<clang::Stmt, clang::Stmt*>();
  }

private:
  StmtMapper() = default;
  StmtMapper(const StmtMapper&) = delete;
  StmtMapper& operator=(const StmtMapper&) = delete;

  NodeMapper<clang::Stmt, clang::Stmt*> mapper_;
};

} // namespace cpptoc
