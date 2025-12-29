/**
 * @file DeclMapper.h
 * @brief Maps C++ source declarations to created C target declarations
 *
 * Single Responsibility: Manage C++ → C declaration mappings for the transpiler.
 *
 * This class enables the Chain of Responsibility pattern by allowing:
 * - Child handlers to store created C declarations
 * - Parent handlers to retrieve C declarations created by child handlers
 *
 * Example:
 * - ParameterHandler creates C ParmVarDecl and stores: declMapper.setCreatedDecl(cppParam, cParam)
 * - FunctionHandler retrieves: cParam = declMapper.getCreatedDecl(cppParam)
 *
 * Design Principles:
 * - Single Responsibility: Only manages declaration mappings
 * - Separation from PathMapper: PathMapper maps file paths, DeclMapper maps declarations
 */

#pragma once

#include "clang/AST/Decl.h"
#include <map>

namespace cpptoc {

/**
 * @class DeclMapper
 * @brief Manages mappings from C++ declarations to created C declarations
 *
 * Responsibilities:
 * - Store C++ → C declaration mappings
 * - Retrieve C declarations for given C++ declarations
 * - Support Chain of Responsibility pattern for handlers
 */
class DeclMapper {
public:
    /**
     * @brief Default constructor
     */
    DeclMapper() = default;

    /**
     * @brief Store mapping from C++ declaration to created C declaration
     * @param cppDecl Source C++ declaration
     * @param cDecl Created C declaration
     *
     * Enables parent handlers to retrieve child declarations created by child handlers.
     *
     * Example:
     * ```cpp
     * // ParameterHandler creates C parameter and stores mapping
     * clang::ParmVarDecl* cParam = createCParameter(...);
     * declMapper.setCreatedDecl(cppParam, cParam);
     *
     * // FunctionHandler retrieves created parameter
     * clang::Decl* cParam = declMapper.getCreatedDecl(cppParam);
     * ```
     */
    void setCreatedDecl(const clang::Decl* cppDecl, clang::Decl* cDecl);

    /**
     * @brief Get C declaration created for a C++ declaration
     * @param cppDecl Source C++ declaration
     * @return Created C declaration, or nullptr if not found
     *
     * Retrieves C declaration previously stored via setCreatedDecl().
     * Returns nullptr if no mapping exists for the given C++ declaration.
     */
    clang::Decl* getCreatedDecl(const clang::Decl* cppDecl) const;

private:
    std::map<const clang::Decl*, clang::Decl*> cppToCDeclMap_;
    ///< Maps C++ source declarations to created C declarations
    ///< Example: C++ ParmVarDecl → C ParmVarDecl
};

} // namespace cpptoc
