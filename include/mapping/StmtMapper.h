/**
 * @file StmtMapper.h
 * @brief Type alias for mapping C++ statements to created C statements
 *
 * This is now a type alias for the generic NodeMapper template.
 * See NodeMapper.h for implementation details.
 *
 * Single Responsibility: Provide statement-specific type alias for NodeMapper.
 *
 * Migration Note:
 * - Old: stmtMapper.setCreatedStmt(cppStmt, cStmt)
 * - New: stmtMapper.setCreated(cppStmt, cStmt)
 * - Old: stmtMapper.getCreatedStmt(cppStmt)
 * - New: stmtMapper.getCreated(cppStmt)
 * - Old: stmtMapper.hasCreatedStmt(cppStmt)
 * - New: stmtMapper.hasCreated(cppStmt)
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

/**
 * @typedef StmtMapper
 * @brief Maps C++ statements to created C statements
 *
 * Type alias for NodeMapper<clang::Stmt, clang::Stmt*>
 *
 * Example:
 * ```cpp
 * StmtMapper stmtMapper;
 * stmtMapper.setCreated(cppCompound, cCompound);
 * clang::Stmt* cStmt = stmtMapper.getCreated(cppCompound);
 * if (stmtMapper.hasCreated(cppCompound)) { ... }
 * ```
 */
using StmtMapper = NodeMapper<clang::Stmt, clang::Stmt*>;

} // namespace cpptoc
