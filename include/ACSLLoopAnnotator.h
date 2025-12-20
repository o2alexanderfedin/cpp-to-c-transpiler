#ifndef ACSL_LOOP_ANNOTATOR_H
#define ACSL_LOOP_ANNOTATOR_H

// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #197: Implement ACSLLoopAnnotator for comprehensive loop annotations
//
// SOLID Principles:
// - Single Responsibility: Generates ACSL loop annotations only
// - Open/Closed: Extends ACSLGenerator base class
// - Liskov Substitution: Can substitute ACSLGenerator where needed
// - Interface Segregation: Focused interface for loop annotation generation
// - Dependency Inversion: Depends on Clang AST abstractions

#include "ACSLGenerator.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include <string>
#include <vector>

/// @brief Generates comprehensive ACSL loop annotations
///
/// Produces complete ACSL loop annotations including:
/// - loop invariant clauses (bounds, array properties, accumulators)
/// - loop variant clauses (termination measures)
/// - loop assigns clauses (side effect tracking within loops)
///
/// Supports common loop patterns:
/// - Array fill: for (i=0; i<n; i++) arr[i] = val;
///   → loop invariant \\forall integer j; 0 <= j < i ==> arr[j] == val;
/// - Accumulator: sum += arr[i];
///   → loop invariant sum == \\sum(0, i-1, \\lambda integer k; arr[k]);
/// - Bounds: Always generate loop invariant 0 <= i <= n;
/// - Variant: for (i=0; i<n; i++) → loop variant n - i;
///
/// ACSL format: Loop annotations appear immediately before loop statements
/// Reference: https://frama-c.com/html/acsl.html (Section 2.4 Loop Annotations)
class ACSLLoopAnnotator : public ACSLGenerator {
public:
  /// @brief Default constructor - inherits ACSL level from base
  ACSLLoopAnnotator();

  /// @brief Constructor with specific ACSL level
  /// @param level ACSL coverage level (Basic or Full)
  explicit ACSLLoopAnnotator(ACSLLevel level);

  /// @brief Constructor with ACSL level and output mode
  /// @param level ACSL coverage level (Basic or Full)
  /// @param mode Output mode (Inline or Separate)
  ACSLLoopAnnotator(ACSLLevel level, ACSLOutputMode mode);

  /// @brief Generate complete ACSL loop annotations
  /// @param loop ForStmt to annotate
  /// @return Complete ACSL loop annotation block as formatted comment
  ///
  /// Example output:
  /// /*@
  ///   loop invariant 0 <= i <= n;
  ///   loop invariant \\forall integer j; 0 <= j < i ==> arr[j] == value;
  ///   loop variant n - i;
  ///   loop assigns i, arr[0..n-1];
  /// */
  std::string generateLoopAnnotations(const clang::ForStmt *loop);

  /// @brief Generate complete ACSL loop annotations for while loop
  /// @param loop WhileStmt to annotate
  /// @return Complete ACSL loop annotation block as formatted comment
  std::string generateLoopAnnotations(const clang::WhileStmt *loop);

  /// @brief Generate complete ACSL loop annotations for do-while loop
  /// @param loop DoStmt to annotate
  /// @return Complete ACSL loop annotation block as formatted comment
  std::string generateLoopAnnotations(const clang::DoStmt *loop);

  /// @brief Generate loop invariant clauses
  /// @param loop Loop statement (ForStmt, WhileStmt, or DoStmt)
  /// @return Vector of loop invariant clause strings (without "loop invariant"
  /// keyword)
  ///
  /// Generated invariants:
  /// - Bounds invariants: 0 <= i <= n
  /// - Array fill pattern: \\forall integer j; 0 <= j < i ==> arr[j] == val
  /// - Accumulator pattern: sum == \\sum(0, i-1, ...)
  /// - Array search: \\forall integer j; 0 <= j < i ==> arr[j] != target
  std::vector<std::string> generateLoopInvariants(const clang::Stmt *loop);

  /// @brief Generate loop variant clause (termination measure)
  /// @param loop Loop statement (ForStmt, WhileStmt, or DoStmt)
  /// @return Loop variant expression string (or empty if not applicable)
  ///
  /// Generated variants:
  /// - Ascending loop: for (i=0; i<n; i++) → n - i
  /// - Descending loop: for (i=n; i>0; i--) → i
  /// - While loop with counter: while (i < n) { i++; } → n - i
  std::string generateLoopVariant(const clang::Stmt *loop);

  /// @brief Generate loop assigns clause (variables/memory modified in loop)
  /// @param loop Loop statement (ForStmt, WhileStmt, or DoStmt)
  /// @return Vector of loop assigns items
  ///
  /// Generated assigns:
  /// - Loop counter: i
  /// - Array elements: arr[0..n-1]
  /// - Pointer dereferences: *ptr
  /// - Struct fields: obj->field
  std::vector<std::string> generateLoopAssigns(const clang::Stmt *loop);

protected:
  /// @brief Detect loop counter variable from ForStmt
  /// @param loop ForStmt to analyze
  /// @return Name of loop counter variable (or empty if not found)
  std::string detectLoopCounter(const clang::ForStmt *loop);

  /// @brief Detect loop bounds from loop condition
  /// @param loop Loop statement
  /// @return Pair of (lower_bound, upper_bound) expressions as strings
  std::pair<std::string, std::string> detectLoopBounds(const clang::Stmt *loop);

  /// @brief Detect array fill pattern in loop body
  /// @param loop Loop statement
  /// @return Array fill invariant string (or empty if pattern not detected)
  ///
  /// Pattern: arr[i] = value;
  /// Invariant: \\forall integer j; 0 <= j < i ==> arr[j] == value
  std::string detectArrayFillPattern(const clang::Stmt *loop);

  /// @brief Detect accumulator pattern in loop body
  /// @param loop Loop statement
  /// @return Accumulator invariant string (or empty if pattern not detected)
  ///
  /// Pattern: sum += expr;
  /// Invariant: sum == initial_value + \\sum(0, i-1, ...)
  std::string detectAccumulatorPattern(const clang::Stmt *loop);

  /// @brief Detect array search pattern in loop body
  /// @param loop Loop statement
  /// @return Search invariant string (or empty if pattern not detected)
  ///
  /// Pattern: if (arr[i] == target) break;
  /// Invariant: \\forall integer j; 0 <= j < i ==> arr[j] != target
  std::string detectArraySearchPattern(const clang::Stmt *loop);

  /// @brief Analyze loop body for variable/memory modifications
  /// @param loop Loop statement
  /// @return Vector of modified variable/memory location names
  std::vector<std::string> trackLoopSideEffects(const clang::Stmt *loop);

  /// @brief Check if loop is ascending (i++ or i += 1)
  /// @param loop Loop statement
  /// @return true if loop counter increases
  bool isAscendingLoop(const clang::Stmt *loop);

  /// @brief Check if loop is descending (i-- or i -= 1)
  /// @param loop Loop statement
  /// @return true if loop counter decreases
  bool isDescendingLoop(const clang::Stmt *loop);

  /// @brief Extract loop body statement
  /// @param loop Loop statement (ForStmt, WhileStmt, or DoStmt)
  /// @return Loop body statement
  const clang::Stmt *getLoopBody(const clang::Stmt *loop);

  /// @brief Extract loop condition expression
  /// @param loop Loop statement
  /// @return Loop condition expression (or nullptr if not found)
  const clang::Expr *getLoopCondition(const clang::Stmt *loop);

  /// @brief Extract loop increment expression (ForStmt only)
  /// @param loop ForStmt
  /// @return Increment expression (or nullptr if not found)
  const clang::Expr *getLoopIncrement(const clang::ForStmt *loop);

  /// @brief Extract counter variable name from loop condition (while/do-while)
  /// @param loop Loop statement (WhileStmt or DoStmt)
  /// @return Counter variable name (e.g., "i", "counter")
  std::string extractCounterFromCondition(const clang::Stmt *loop);

private:
  /// @brief Helper: Format loop assigns clause items into single string
  /// @param items Vector of individual assign locations
  /// @return Formatted assigns clause (e.g., "i, arr[0..n-1]")
  std::string formatLoopAssignsClause(const std::vector<std::string> &items);

  /// @brief Helper: Get variable name from DeclRefExpr
  /// @param expr Expression to analyze
  /// @return Variable name or empty string
  std::string getVariableName(const clang::Expr *expr);

  /// @brief Helper: Check if expression is array subscript
  /// @param expr Expression to check
  /// @return true if expr is ArraySubscriptExpr
  bool isArraySubscript(const clang::Expr *expr);

  /// @brief Helper: Extract array name from ArraySubscriptExpr
  /// @param expr ArraySubscriptExpr to analyze
  /// @return Array base name
  std::string getArrayBaseName(const clang::Expr *expr);
};

#endif // ACSL_LOOP_ANNOTATOR_H
