/**
 * @file TypeMapper.h
 * @brief Singleton wrapper for mapping C++ types to created C types
 *
 * This provides a singleton wrapper around NodeMapper to ensure all source files
 * share the same mapping instance during a transpilation session.
 *
 * Single Responsibility: Provide type-specific singleton mapper for NodeMapper.
 *
 * Migration Note:
 * - Old: TypeMapper typeMapper;
 * - New: TypeMapper& typeMapper = TypeMapper::getInstance();
 * - Usage: typeMapper.setCreated(cppType, cType)
 * - Usage: typeMapper.getCreated(cppType)
 * - Usage: typeMapper.hasCreated(cppType)
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Type.h"

namespace cpptoc {

/**
 * @class TypeMapper
 * @brief Singleton wrapper for mapping C++ types to created C types
 *
 * Wraps NodeMapper<clang::Type, clang::QualType> in a singleton pattern to ensure
 * all source files share the same type mappings during transpilation.
 *
 * Note: ValueT is QualType (value type), not QualType* (pointer)
 * QualType is a lightweight handle that acts like a pointer internally.
 *
 * Example:
 * ```cpp
 * TypeMapper& typeMapper = TypeMapper::getInstance();
 * typeMapper.setCreated(cppRefType, cPtrType);
 * clang::QualType cType = typeMapper.getCreated(cppRefType);
 * if (typeMapper.hasCreated(cppRefType)) { ... }
 * ```
 */
class TypeMapper {
public:
  /**
   * @brief Get the singleton TypeMapper instance
   * @return Reference to the global TypeMapper instance
   *
   * **Singleton Pattern**: Ensures all files share the same TypeMapper
   * **Thread Safety**: Not thread-safe; call from single thread during transpilation
   */
  static TypeMapper& getInstance() {
    static TypeMapper instance;
    return instance;
  }

  /**
   * @brief Store mapping from C++ type to created C type
   * @param cppNode Source C++ type
   * @param cNode Created C type (QualType)
   */
  void setCreated(const clang::Type* cppNode, clang::QualType cNode) {
    mapper_.setCreated(cppNode, cNode);
  }

  /**
   * @brief Get C type created for a C++ type
   * @param cppNode Source C++ type
   * @return Created C type, or null QualType if not found
   */
  clang::QualType getCreated(const clang::Type* cppNode) const {
    return mapper_.getCreated(cppNode);
  }

  /**
   * @brief Check if a C++ type has a mapped C type
   * @param cppNode Source C++ type
   * @return true if mapping exists, false otherwise
   */
  bool hasCreated(const clang::Type* cppNode) const {
    return mapper_.hasCreated(cppNode);
  }

  /**
   * @brief Reset all mappings (for testing)
   */
  static void reset() {
    getInstance().mapper_ = NodeMapper<clang::Type, clang::QualType>();
  }

private:
  TypeMapper() = default;
  TypeMapper(const TypeMapper&) = delete;
  TypeMapper& operator=(const TypeMapper&) = delete;

  NodeMapper<clang::Type, clang::QualType> mapper_;
};

} // namespace cpptoc
