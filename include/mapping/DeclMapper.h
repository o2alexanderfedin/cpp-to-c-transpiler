/**
 * @file DeclMapper.h
 * @brief Type alias for mapping C++ declarations to created C declarations
 *
 * This is now a type alias for the generic NodeMapper template.
 * See NodeMapper.h for implementation details.
 *
 * Single Responsibility: Provide declaration-specific type alias for NodeMapper.
 *
 * Migration Note:
 * - Old: declMapper.setCreatedDecl(cppDecl, cDecl)
 * - New: declMapper.setCreated(cppDecl, cDecl)
 * - Old: declMapper.getCreatedDecl(cppDecl)
 * - New: declMapper.getCreated(cppDecl)
 * - New: declMapper.hasCreated(cppDecl) [previously missing]
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Decl.h"

namespace cpptoc {

/**
 * @typedef DeclMapper
 * @brief Maps C++ declarations to created C declarations
 *
 * Type alias for NodeMapper<clang::Decl, clang::Decl*>
 *
 * Example:
 * ```cpp
 * DeclMapper declMapper;
 * declMapper.setCreated(cppParam, cParam);
 * clang::Decl* cParam = declMapper.getCreated(cppParam);
 * if (declMapper.hasCreated(cppParam)) { ... }
 * ```
 */
using DeclMapper = NodeMapper<clang::Decl, clang::Decl*>;

} // namespace cpptoc
