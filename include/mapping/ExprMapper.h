/**
 * @file ExprMapper.h
 * @brief Type alias for mapping C++ expressions to created C expressions
 *
 * This is now a type alias for the generic NodeMapper template.
 * See NodeMapper.h for implementation details.
 *
 * Single Responsibility: Provide expression-specific type alias for NodeMapper.
 *
 * Migration Note:
 * - Old: exprMapper.setCreatedExpr(cppExpr, cExpr)
 * - New: exprMapper.setCreated(cppExpr, cExpr)
 * - Old: exprMapper.getCreatedExpr(cppExpr)
 * - New: exprMapper.getCreated(cppExpr)
 * - Old: exprMapper.hasCreatedExpr(cppExpr)
 * - New: exprMapper.hasCreated(cppExpr)
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @typedef ExprMapper
 * @brief Maps C++ expressions to created C expressions
 *
 * Type alias for NodeMapper<clang::Expr, clang::Expr*>
 *
 * Example:
 * ```cpp
 * ExprMapper exprMapper;
 * exprMapper.setCreated(cppBinOp, cBinOp);
 * clang::Expr* cExpr = exprMapper.getCreated(cppBinOp);
 * if (exprMapper.hasCreated(cppBinOp)) { ... }
 * ```
 */
using ExprMapper = NodeMapper<clang::Expr, clang::Expr*>;

} // namespace cpptoc
