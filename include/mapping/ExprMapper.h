/**
 * @file ExprMapper.h
 * @brief RAII mapper for C++ expressions to created C expressions
 *
 * This provides a per-instance mapper around NodeMapper using RAII pattern.
 * Each instance maintains its own mapping state.
 *
 * Single Responsibility: Provide expression-specific mapper for NodeMapper.
 *
 * Usage:
 * - Create: ExprMapper exprMapper;
 * - Usage: exprMapper.setCreated(cppExpr, cExpr)
 * - Usage: exprMapper.getCreated(cppExpr)
 * - Usage: exprMapper.hasCreated(cppExpr)
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @class ExprMapper
 * @brief RAII wrapper for mapping C++ expressions to created C expressions
 *
 * Wraps NodeMapper<clang::Expr, clang::Expr*> with RAII semantics.
 * Each test/thread creates its own instance for complete isolation.
 *
 * Example:
 * ```cpp
 * auto exprMapper = std::make_unique<ExprMapper>();
 * exprMapper->setCreated(cppBinOp, cBinOp);
 * clang::Expr* cExpr = exprMapper->getCreated(cppBinOp);
 * if (exprMapper->hasCreated(cppBinOp)) { ... }
 * ```
 */
class ExprMapper {
public:
  /**
   * @brief Public constructor for RAII pattern
   *
   * **RAII Pattern**: Each test creates its own ExprMapper instance
   * **Thread Safety**: Each thread/test has isolated instance - fully thread-safe
   */
  ExprMapper() = default;

  /**
   * @brief Store mapping from C++ expression to created C expression
   * @param cppNode Source C++ expression
   * @param cNode Created C expression
   */
  void setCreated(const clang::Expr* cppNode, clang::Expr* cNode) {
    mapper_.setCreated(cppNode, cNode);
  }

  /**
   * @brief Get C expression created for a C++ expression
   * @param cppNode Source C++ expression
   * @return Created C expression, or nullptr if not found
   */
  clang::Expr* getCreated(const clang::Expr* cppNode) const {
    return mapper_.getCreated(cppNode);
  }

  /**
   * @brief Check if a C++ expression has a mapped C expression
   * @param cppNode Source C++ expression
   * @return true if mapping exists, false otherwise
   */
  bool hasCreated(const clang::Expr* cppNode) const {
    return mapper_.hasCreated(cppNode);
  }

  // Prevent copying (use move semantics or unique_ptr instead)
  ExprMapper(const ExprMapper&) = delete;
  ExprMapper& operator=(const ExprMapper&) = delete;

  // Allow move semantics for modern C++
  ExprMapper(ExprMapper&&) = default;
  ExprMapper& operator=(ExprMapper&&) = default;

private:
  NodeMapper<clang::Expr, clang::Expr*> mapper_;
};

} // namespace cpptoc
