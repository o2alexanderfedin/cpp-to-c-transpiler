/**
 * @file TypeMapper.h
 * @brief Type alias for mapping C++ types to created C types
 *
 * This is now a type alias for the generic NodeMapper template.
 * See NodeMapper.h for implementation details.
 *
 * Single Responsibility: Provide type-specific type alias for NodeMapper.
 *
 * Migration Note:
 * - Old: typeMapper.setCreatedType(cppType, cType)
 * - New: typeMapper.setCreated(cppType, cType)
 * - Old: typeMapper.getCreatedType(cppType)
 * - New: typeMapper.getCreated(cppType)
 * - Old: typeMapper.hasCreatedType(cppType)
 * - New: typeMapper.hasCreated(cppType)
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Type.h"

namespace cpptoc {

/**
 * @typedef TypeMapper
 * @brief Maps C++ types to created C types
 *
 * Type alias for NodeMapper<clang::Type, clang::QualType>
 *
 * Note: ValueT is QualType (value type), not QualType* (pointer)
 * QualType is a lightweight handle that acts like a pointer internally.
 *
 * Example:
 * ```cpp
 * TypeMapper typeMapper;
 * typeMapper.setCreated(cppRefType, cPtrType);
 * clang::QualType cType = typeMapper.getCreated(cppRefType);
 * if (typeMapper.hasCreated(cppRefType)) { ... }
 * ```
 */
using TypeMapper = NodeMapper<clang::Type, clang::QualType>;

} // namespace cpptoc
