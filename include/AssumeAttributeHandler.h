// Phase 3: [[assume]] Attribute Handling (C++23 P1774R8)
// Single Responsibility: Handle C++23 [[assume(condition)]] attribute translation
// Open/Closed: Extensible to new strategies without modifying core logic

#ifndef ASSUME_ATTRIBUTE_HANDLER_H
#define ASSUME_ATTRIBUTE_HANDLER_H

#include "clang/AST/AST.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Stmt.h"
#include "CNodeBuilder.h"
#include <string>

// Strategy pattern for handling [[assume]] attributes
enum class AssumeStrategy {
  Strip,    // Remove attribute entirely (safest, minimal output)
  Comment,  // Convert to comment: /* assume: condition */ (informative, default)
  Builtin   // Convert to __builtin_assume(condition) (preserve optimization hint)
};

/**
 * @brief Handler for C++23 [[assume(condition)]] attribute (P1774R8)
 *
 * Single Responsibility: Translate [[assume]] attributes to C equivalents
 * Dependency Inversion: Depends on abstract CNodeBuilder, not concrete implementation
 *
 * The [[assume]] attribute is an optimization hint that doesn't affect semantics.
 * This handler provides three strategies:
 *
 * 1. Strip: Remove the attribute entirely
 *    - Safest option, minimal C output
 *    - Semantics unchanged (assume is hint-only)
 *
 * 2. Comment: Convert to C comment
 *    - Documents programmer's assumptions
 *    - Helps C code readers understand intent
 *    - Default strategy
 *
 * 3. Builtin: Convert to __builtin_assume()
 *    - Preserves optimization hint for GCC/Clang
 *    - Not portable to all C compilers
 *    - May improve generated code performance
 */
class AssumeAttributeHandler {
public:
  /**
   * @brief Construct handler with specified strategy
   * @param Builder CNodeBuilder for creating C AST nodes
   * @param Strategy Transformation strategy (default: Comment)
   */
  explicit AssumeAttributeHandler(clang::CNodeBuilder& Builder,
                                   AssumeStrategy Strategy = AssumeStrategy::Comment);

  /**
   * @brief Handle [[assume(condition)]] attributed statement
   * @param S AttributedStmt containing assume attribute
   * @param Ctx ASTContext for creating new nodes
   * @return Transformed statement (or nullptr on error)
   *
   * Single Responsibility: Orchestrate attribute transformation
   * Template Method Pattern: Strategy determines transformation details
   */
  clang::Stmt* handle(clang::AttributedStmt* S, clang::ASTContext& Ctx);

private:
  clang::CNodeBuilder& m_builder;
  AssumeStrategy m_strategy;

  /**
   * @brief Extract condition expression from assume attribute
   * @param S AttributedStmt containing assume attribute
   * @return Condition expression, or nullptr if not found
   */
  clang::Expr* extractCondition(clang::AttributedStmt* S);

  /**
   * @brief Convert expression to C-compatible string representation
   * @param E Expression to convert
   * @param Ctx ASTContext for type information
   * @return String representation of expression in C syntax
   *
   * Handles translation of C++ expressions to C:
   * - nullptr -> NULL or ((void*)0)
   * - C++ operators -> C equivalents
   * - Type casts -> C-style casts
   */
  std::string expressionToString(clang::Expr* E, clang::ASTContext& Ctx);

  /**
   * @brief Create __builtin_assume() call expression
   * @param Condition The condition expression
   * @param Ctx ASTContext for creating new nodes
   * @return CallExpr for __builtin_assume(condition)
   */
  clang::CallExpr* createBuiltinAssumeCall(clang::Expr* Condition,
                                            clang::ASTContext& Ctx);

  /**
   * @brief Create compound statement with comment attached
   * @param Stmt Underlying statement
   * @param Comment Comment text to attach
   * @param Ctx ASTContext for creating new nodes
   * @return Statement with comment (implementation-specific)
   *
   * Note: Clang doesn't preserve comments in AST by default.
   * This method may need to use raw text rewriting or
   * store comments separately for emission during code generation.
   */
  clang::Stmt* createCommentedStmt(clang::Stmt* Stmt,
                                    const std::string& Comment,
                                    clang::ASTContext& Ctx);

  /**
   * @brief Check if expression has side effects
   * @param E Expression to analyze
   * @param Ctx ASTContext for analysis
   * @return true if expression has side effects
   *
   * Side effects include:
   * - Function calls (unless pure)
   * - Assignment operators
   * - Increment/decrement operators
   * - volatile access
   *
   * If condition has side effects, we should warn and strip the assume.
   */
  bool hasSideEffects(clang::Expr* E, clang::ASTContext& Ctx);

  /**
   * @brief Get the assume attribute from attributed statement
   * @param S AttributedStmt to search
   * @return Assume attribute, or nullptr if not found
   */
  const clang::Attr* getAssumeAttr(clang::AttributedStmt* S);

  /**
   * @brief Handle Strip strategy - remove attribute
   * @param S AttributedStmt to process
   * @return Underlying statement without attribute
   */
  clang::Stmt* handleStrip(clang::AttributedStmt* S);

  /**
   * @brief Handle Comment strategy - convert to comment
   * @param S AttributedStmt to process
   * @param Ctx ASTContext for creating new nodes
   * @return Statement with comment attached
   */
  clang::Stmt* handleComment(clang::AttributedStmt* S, clang::ASTContext& Ctx);

  /**
   * @brief Handle Builtin strategy - convert to __builtin_assume()
   * @param S AttributedStmt to process
   * @param Ctx ASTContext for creating new nodes
   * @return CompoundStmt containing builtin call and underlying statement
   */
  clang::Stmt* handleBuiltin(clang::AttributedStmt* S, clang::ASTContext& Ctx);
};

#endif // ASSUME_ATTRIBUTE_HANDLER_H
