/**
 * @file TypeMapper.h
 * @brief Maps C++ source types to created C target types
 *
 * Single Responsibility: Manage C++ → C type mappings for the transpiler.
 *
 * This class enables the Chain of Responsibility pattern by allowing:
 * - TypeHandler to store created C types
 * - Other handlers to retrieve C types created by TypeHandler
 *
 * Example:
 * - TypeHandler creates C pointer type and stores: typeMapper.setCreatedType(cppRefType, cPtrType)
 * - FunctionHandler retrieves: cPtrType = typeMapper.getCreatedType(cppRefType)
 *
 * Design Principles:
 * - Single Responsibility: Only manages type mappings
 * - Separation from DeclMapper: DeclMapper maps declarations, TypeMapper maps types
 */

#pragma once

#include "clang/AST/Type.h"
#include <map>

namespace cpptoc {

/**
 * @class TypeMapper
 * @brief Manages mappings from C++ types to created C types
 *
 * Responsibilities:
 * - Store C++ → C type mappings
 * - Retrieve C types for given C++ types
 * - Support Chain of Responsibility pattern for handlers
 */
class TypeMapper {
public:
    /**
     * @brief Default constructor
     */
    TypeMapper() = default;

    /**
     * @brief Store mapping from C++ type to created C type
     * @param cppType Source C++ type
     * @param cType Created C type
     *
     * Enables handlers to retrieve types created by TypeHandler.
     *
     * Example:
     * ```cpp
     * // TypeHandler creates C pointer type and stores mapping
     * clang::QualType cPtrType = createPointerType(...);
     * typeMapper.setCreatedType(cppRefType, cPtrType);
     *
     * // FunctionHandler retrieves created type
     * clang::QualType cType = typeMapper.getCreatedType(cppRefType);
     * ```
     */
    void setCreatedType(const clang::Type* cppType, clang::QualType cType);

    /**
     * @brief Get C type created for a C++ type
     * @param cppType Source C++ type
     * @return Created C type, or null QualType if not found
     *
     * Retrieves C type previously stored via setCreatedType().
     * Returns null QualType if no mapping exists for the given C++ type.
     */
    clang::QualType getCreatedType(const clang::Type* cppType) const;

    /**
     * @brief Check if a C++ type has a mapped C type
     * @param cppType Source C++ type
     * @return true if mapping exists, false otherwise
     */
    bool hasCreatedType(const clang::Type* cppType) const;

private:
    std::map<const clang::Type*, clang::QualType> cppToCTypeMap_;
    ///< Maps C++ source types to created C types
    ///< Example: C++ LValueReferenceType → C PointerType
};

} // namespace cpptoc
