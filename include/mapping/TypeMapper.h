/**
 * @file TypeMapper.h
 * @brief RAII mapper for C++ types to created C types
 *
 * This provides a per-instance mapper around NodeMapper using RAII pattern.
 * Each instance maintains its own mapping state.
 *
 * Single Responsibility: Provide type-specific mapper for NodeMapper.
 *
 * Usage:
 * - Create: TypeMapper typeMapper;
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
 * @brief RAII wrapper for mapping C++ types to created C types
 *
 * Wraps NodeMapper<clang::Type, clang::QualType> with RAII semantics.
 * Each test/thread creates its own instance for complete isolation.
 *
 * Note: ValueT is QualType (value type), not QualType* (pointer)
 * QualType is a lightweight handle that acts like a pointer internally.
 *
 * Example:
 * ```cpp
 * auto typeMapper = std::make_unique<TypeMapper>();
 * typeMapper->setCreated(cppRefType, cPtrType);
 * clang::QualType cType = typeMapper->getCreated(cppRefType);
 * if (typeMapper->hasCreated(cppRefType)) { ... }
 * ```
 */
class TypeMapper {
public:
  /**
   * @brief Public constructor for RAII pattern
   *
   * **RAII Pattern**: Each test creates its own TypeMapper instance
   * **Thread Safety**: Each thread/test has isolated instance - fully thread-safe
   */
  TypeMapper() = default;

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

  // Prevent copying (use move semantics or unique_ptr instead)
  TypeMapper(const TypeMapper&) = delete;
  TypeMapper& operator=(const TypeMapper&) = delete;

  // Allow move semantics for modern C++
  TypeMapper(TypeMapper&&) = default;
  TypeMapper& operator=(TypeMapper&&) = default;

private:
  NodeMapper<clang::Type, clang::QualType> mapper_;
};

} // namespace cpptoc
