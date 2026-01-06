/**
 * @file DeclMapper.h
 * @brief RAII mapper for C++ declarations to created C declarations
 *
 * This provides a per-instance mapper around NodeMapper using RAII pattern.
 * Each instance maintains its own mapping state.
 *
 * Single Responsibility: Provide declaration-specific mapper for NodeMapper.
 *
 * Usage:
 * - Create: DeclMapper declMapper;
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
 * @brief RAII wrapper for mapping C++ declarations to created C declarations
 *
 * Wraps NodeMapper<clang::Decl, clang::Decl*> with RAII semantics.
 * Each test/thread creates its own instance for complete isolation.
 *
 * Example:
 * ```cpp
 * auto declMapper = std::make_unique<DeclMapper>();
 * declMapper->setCreated(cppParam, cParam);
 * clang::Decl* cParam = declMapper->getCreated(cppParam);
 * if (declMapper->hasCreated(cppParam)) { ... }
 * ```
 */
class DeclMapper {
public:
  /**
   * @brief Public constructor for RAII pattern
   *
   * **RAII Pattern**: Each test creates its own DeclMapper instance
   * **Thread Safety**: Each thread/test has isolated instance - fully thread-safe
   */
  DeclMapper() = default;

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

  // Prevent copying (use move semantics or unique_ptr instead)
  DeclMapper(const DeclMapper&) = delete;
  DeclMapper& operator=(const DeclMapper&) = delete;

  // Allow move semantics for modern C++
  DeclMapper(DeclMapper&&) = default;
  DeclMapper& operator=(DeclMapper&&) = default;

private:
  NodeMapper<clang::Decl, clang::Decl*> mapper_;
};

} // namespace cpptoc
