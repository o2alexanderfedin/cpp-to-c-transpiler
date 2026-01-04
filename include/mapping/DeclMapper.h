/**
 * @file DeclMapper.h
 * @brief Singleton wrapper for mapping C++ declarations to created C declarations
 *
 * This provides a singleton wrapper around NodeMapper to ensure all source files
 * share the same mapping instance during a transpilation session.
 *
 * Single Responsibility: Provide declaration-specific singleton mapper for NodeMapper.
 *
 * Migration Note:
 * - Old: DeclMapper declMapper;
 * - New: DeclMapper& declMapper = DeclMapper::getInstance();
 * - Usage: declMapper.setCreated(cppDecl, cDecl)
 * - Usage: declMapper.getCreated(cppDecl)
 * - Usage: declMapper.hasCreated(cppDecl)
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Decl.h"

namespace cpptoc {

/**
 * @class DeclMapper
 * @brief Singleton wrapper for mapping C++ declarations to created C declarations
 *
 * Wraps NodeMapper<clang::Decl, clang::Decl*> in a singleton pattern to ensure
 * all source files share the same declaration mappings during transpilation.
 *
 * Example:
 * ```cpp
 * DeclMapper& declMapper = DeclMapper::getInstance();
 * declMapper.setCreated(cppParam, cParam);
 * clang::Decl* cParam = declMapper.getCreated(cppParam);
 * if (declMapper.hasCreated(cppParam)) { ... }
 * ```
 */
class DeclMapper {
public:
  /**
   * @brief Get the singleton DeclMapper instance
   * @return Reference to the global DeclMapper instance
   *
   * **Singleton Pattern**: Ensures all files share the same DeclMapper
   * **Thread Safety**: Not thread-safe; call from single thread during transpilation
   */
  static DeclMapper& getInstance() {
    static DeclMapper instance;
    return instance;
  }

  /**
   * @brief Store mapping from C++ node to created C node
   * @param cppNode Source C++ AST node
   * @param cNode Created C AST node
   */
  void setCreated(const clang::Decl* cppNode, clang::Decl* cNode) {
    mapper_.setCreated(cppNode, cNode);
  }

  /**
   * @brief Get C node created for a C++ node
   * @param cppNode Source C++ AST node
   * @return Created C node, or nullptr if not found
   */
  clang::Decl* getCreated(const clang::Decl* cppNode) const {
    return mapper_.getCreated(cppNode);
  }

  /**
   * @brief Check if a C++ node has a mapped C node
   * @param cppNode Source C++ AST node
   * @return true if mapping exists, false otherwise
   */
  bool hasCreated(const clang::Decl* cppNode) const {
    return mapper_.hasCreated(cppNode);
  }

  /**
   * @brief Reset all mappings (for testing)
   */
  static void reset() {
    getInstance().mapper_ = NodeMapper<clang::Decl, clang::Decl*>();
  }

private:
  DeclMapper() = default;
  DeclMapper(const DeclMapper&) = delete;
  DeclMapper& operator=(const DeclMapper&) = delete;

  NodeMapper<clang::Decl, clang::Decl*> mapper_;
};

} // namespace cpptoc
