/**
 * @file FieldOffsetMapper.h
 * @brief Maps C struct fields to their offsets for constructor generation
 *
 * This provides field offset storage calculated during RecordHandler struct generation.
 * ConstructorHandler uses these offsets when calculating base constructor call pointers.
 *
 * Single Responsibility: Store and retrieve C struct field offsets.
 *
 * Usage:
 * - RecordHandler: offsetMapper.setFieldOffset(cRecordDecl, "b_data", 0)
 * - ConstructorHandler: unsigned offset = offsetMapper.getFieldOffset(cRecordDecl, "b_data")
 */

#pragma once

#include <map>
#include <string>

// Forward declarations
namespace clang {
  class RecordDecl;
}

namespace cpptoc {

/**
 * @class FieldOffsetMapper
 * @brief Maps (C RecordDecl, field name) to byte offset
 *
 * Stores field offsets calculated from C struct layouts during RecordHandler.
 * These offsets are used by ConstructorHandler to calculate base constructor
 * call pointer arithmetic.
 *
 * Example:
 * ```cpp
 * // During RecordHandler (struct generation):
 * offsetMapper.setFieldOffset(cStructD, "b_data", 0);
 * offsetMapper.setFieldOffset(cStructD, "c_data", 4);
 * offsetMapper.setFieldOffset(cStructD, "d_data", 8);
 * offsetMapper.setFieldOffset(cStructD, "a_data", 12);
 *
 * // During ConstructorHandler (base constructor calls):
 * unsigned offset = offsetMapper.getFieldOffset(cStructD, "c_data"); // Returns 4
 * ```
 */
class FieldOffsetMapper {
public:
  /**
   * @brief Public constructor for RAII pattern
   *
   * **RAII Pattern**: Each test creates its own FieldOffsetMapper instance
   * **Thread Safety**: Each thread/test has isolated instance - fully thread-safe
   */
  FieldOffsetMapper() = default;

  /**
   * @brief Store field offset for a C struct field
   * @param cRecordDecl C struct RecordDecl
   * @param fieldName Field name (e.g., "b_data", "c_data")
   * @param offset Byte offset of field from start of struct
   */
  void setFieldOffset(const clang::RecordDecl* cRecordDecl, const std::string& fieldName, unsigned offset) {
    structFieldOffsets_[cRecordDecl][fieldName] = offset;
  }

  /**
   * @brief Get field offset for a C struct field
   * @param cRecordDecl C struct RecordDecl
   * @param fieldName Field name to look up
   * @return Byte offset, or 0 if not found
   */
  unsigned getFieldOffset(const clang::RecordDecl* cRecordDecl, const std::string& fieldName) const {
    auto structIt = structFieldOffsets_.find(cRecordDecl);
    if (structIt == structFieldOffsets_.end()) {
      return 0;
    }
    auto fieldIt = structIt->second.find(fieldName);
    if (fieldIt == structIt->second.end()) {
      return 0;
    }
    return fieldIt->second;
  }

  /**
   * @brief Check if a field offset exists
   * @param cRecordDecl C struct RecordDecl
   * @param fieldName Field name to check
   * @return true if offset is stored, false otherwise
   */
  bool hasFieldOffset(const clang::RecordDecl* cRecordDecl, const std::string& fieldName) const {
    auto structIt = structFieldOffsets_.find(cRecordDecl);
    if (structIt == structFieldOffsets_.end()) {
      return false;
    }
    return structIt->second.find(fieldName) != structIt->second.end();
  }

  // Prevent copying (use move semantics or unique_ptr instead)
  FieldOffsetMapper(const FieldOffsetMapper&) = delete;
  FieldOffsetMapper& operator=(const FieldOffsetMapper&) = delete;

  // Allow move semantics for modern C++
  FieldOffsetMapper(FieldOffsetMapper&&) = default;
  FieldOffsetMapper& operator=(FieldOffsetMapper&&) = default;

private:
  // Map: C RecordDecl → (field name → offset)
  std::map<const clang::RecordDecl*, std::map<std::string, unsigned>> structFieldOffsets_;
};

} // namespace cpptoc
