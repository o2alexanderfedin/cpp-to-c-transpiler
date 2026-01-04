/**
 * @file ExprMapper.h
 * @brief Singleton wrapper for mapping C++ expressions to created C expressions
 *
 * This provides a singleton wrapper around NodeMapper to ensure all source files
 * share the same mapping instance during a transpilation session.
 *
 * Single Responsibility: Provide expression-specific singleton mapper for NodeMapper.
 *
 * Migration Note:
 * - Old: ExprMapper exprMapper;
 * - New: ExprMapper& exprMapper = ExprMapper::getInstance();
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
 * @brief Singleton wrapper for mapping C++ expressions to created C expressions
 *
 * Wraps NodeMapper<clang::Expr, clang::Expr*> in a singleton pattern to ensure
 * all source files share the same expression mappings during transpilation.
 *
 * Example:
 * ```cpp
 * ExprMapper& exprMapper = ExprMapper::getInstance();
 * exprMapper.setCreated(cppBinOp, cBinOp);
 * clang::Expr* cExpr = exprMapper.getCreated(cppBinOp);
 * if (exprMapper.hasCreated(cppBinOp)) { ... }
 * ```
 */
class ExprMapper {
public:
  /**
   * @brief Get the singleton ExprMapper instance
   * @return Reference to the global ExprMapper instance
   *
   * **Singleton Pattern**: Ensures all files share the same ExprMapper
   * **Thread Safety**: Not thread-safe; call from single thread during transpilation
   */
  static ExprMapper& getInstance() {
    static ExprMapper instance;
    return instance;
  }

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

  /**
   * @brief Reset all mappings (for testing)
   */
  static void reset() {
    getInstance().mapper_ = NodeMapper<clang::Expr, clang::Expr*>();
  }

private:
  ExprMapper() = default;
  ExprMapper(const ExprMapper&) = delete;
  ExprMapper& operator=(const ExprMapper&) = delete;

  NodeMapper<clang::Expr, clang::Expr*> mapper_;
};

} // namespace cpptoc
