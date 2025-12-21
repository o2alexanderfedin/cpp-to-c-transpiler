#ifndef ACSL_BEHAVIOR_ANNOTATOR_H
#define ACSL_BEHAVIOR_ANNOTATOR_H

// Phase 5 (v1.22.0): ACSL Function Behaviors
// Plan: .planning/phases/05-function-behaviors/PLAN.md
//
// SOLID Principles:
// - Single Responsibility: Generates ACSL function behaviors only
// - Open/Closed: Extends ACSLGenerator base class
// - Liskov Substitution: Can substitute ACSLGenerator where needed
// - Interface Segregation: Focused interface for behavior generation
// - Dependency Inversion: Depends on Clang AST abstractions

#include "ACSLGenerator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include <string>
#include <vector>

/// @brief Represents a single ACSL behavior
///
/// A behavior consists of:
/// - Name: Unique identifier for the behavior
/// - Assumes clause: Precondition for this behavior path
/// - Ensures clauses: Postconditions for this behavior path
///
/// Example:
/// behavior null_ptr:
///   assumes p == \null;
///   ensures \result == -1;
struct Behavior {
    std::string name;                  ///< Behavior name (e.g., "null_ptr", "valid_ptr")
    std::string assumesClause;         ///< Precondition (e.g., "p == \null")
    std::vector<std::string> ensuresClauses;  ///< Postconditions
};

/// @brief Generates ACSL function behaviors from control flow analysis
///
/// Behaviors represent different execution paths based on function preconditions.
/// Each behavior has:
/// - assumes clause: Condition that triggers this path
/// - ensures clause: Guarantees when this path executes
///
/// Key features:
/// - Extract behaviors from if/else statements
/// - Extract behaviors from switch statements
/// - Detect error vs. normal paths
/// - Check completeness (all cases covered)
/// - Check disjointness (no overlapping behaviors)
/// - Handle nested conditions
/// - Support multiple return points
///
/// ACSL format: Behaviors appear in function contracts
/// Reference: https://frama-c.com/html/acsl.html (v1.22+)
///
/// Example output:
/// /*@
///   requires \valid(p) || p == \null;
///   behavior null_ptr:
///     assumes p == \null;
///     ensures \result == -1;
///   behavior valid_ptr:
///     assumes p != \null && \valid(p);
///     ensures \result == *\old(p);
///   complete behaviors;
///   disjoint behaviors;
/// */
class ACSLBehaviorAnnotator : public ACSLGenerator {
    // Allow BehaviorExtractor to access protected methods
    friend class BehaviorExtractor;

public:
    /// @brief Default constructor - inherits ACSL level from base
    ACSLBehaviorAnnotator();

    /// @brief Constructor with specific ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLBehaviorAnnotator(ACSLLevel level);

    /// @brief Generate ACSL behaviors from function control flow
    /// @param func Function declaration to analyze
    /// @return ACSL behavior annotation string
    ///
    /// Analyzes function body to extract conditional paths and
    /// generates corresponding ACSL behaviors with assumes/ensures clauses.
    std::string generateBehaviors(const clang::FunctionDecl* func);

    /// @brief Check if behaviors are complete (all cases covered)
    /// @param func Function declaration to analyze
    /// @return true if all input cases are covered by behaviors
    ///
    /// Complete behaviors mean every possible input satisfies at least
    /// one behavior's assumes clause. For example, if x is int:
    /// - (x >= 0) and (x < 0) → complete
    /// - (x > 0) and (x < 0) → incomplete (missing x == 0)
    bool checkCompleteness(const clang::FunctionDecl* func);

    /// @brief Check if behaviors are disjoint (no overlapping conditions)
    /// @param func Function declaration to analyze
    /// @return true if no two behaviors can execute simultaneously
    ///
    /// Disjoint behaviors mean no input can satisfy multiple assumes clauses.
    /// For example:
    /// - (x > 0) and (x <= 0) → disjoint
    /// - (x > 0) and (x >= 0) → not disjoint (overlap at x > 0)
    bool checkDisjointness(const clang::FunctionDecl* func);

protected:
    /// @brief Extract behaviors from if/else statements
    /// @param func Function declaration
    /// @return Vector of extracted behaviors
    ///
    /// Analyzes if/else control flow to identify distinct execution paths.
    /// Each path becomes a behavior with appropriate assumes/ensures clauses.
    std::vector<Behavior> extractBehaviorsFromIfElse(const clang::FunctionDecl* func);

    /// @brief Extract behaviors from switch statements
    /// @param func Function declaration
    /// @return Vector of extracted behaviors
    ///
    /// Each switch case becomes a behavior with assumes clause matching
    /// the case value and ensures clause for that path's result.
    std::vector<Behavior> extractBehaviorsFromSwitch(const clang::FunctionDecl* func);

    /// @brief Extract behaviors from nested conditionals
    /// @param func Function declaration
    /// @return Vector of extracted behaviors with compound conditions
    ///
    /// Handles nested if/else by combining conditions with &&.
    /// Example: if (x > 0) { if (y > 0) ... }
    /// → behavior: assumes x > 0 && y > 0
    std::vector<Behavior> extractBehaviorsFromNestedConditions(const clang::FunctionDecl* func);

    /// @brief Generate assumes clause from condition expression
    /// @param condition AST expression representing the condition
    /// @return ACSL assumes clause string
    ///
    /// Converts C++ condition to ACSL assumes syntax:
    /// - nullptr → \null
    /// - Pointer comparisons → ACSL pointer logic
    /// - Numeric ranges → ACSL expressions
    std::string generateAssumesClause(const clang::Expr* condition);

    /// @brief Generate ensures clause for a behavior
    /// @param func Function declaration
    /// @param behavior Behavior to generate ensures for
    /// @param returnStmt Return statement in this behavior path
    /// @return ACSL ensures clause string
    ///
    /// Analyzes return value and side effects for this behavior path.
    /// Generates postconditions specific to this behavior.
    std::string generateEnsuresForBehavior(const clang::FunctionDecl* func,
                                            const Behavior& behavior,
                                            const clang::ReturnStmt* returnStmt);

    /// @brief Detect if a behavior represents an error path
    /// @param behavior Behavior to analyze
    /// @return true if this is an error path (returns error code, null, etc.)
    ///
    /// Error paths typically:
    /// - Return -1, nullptr, false
    /// - Check for null pointers
    /// - Check for invalid ranges
    bool isErrorBehavior(const Behavior& behavior);

    /// @brief Detect if a behavior represents a normal/success path
    /// @param behavior Behavior to analyze
    /// @return true if this is a normal execution path
    bool isNormalBehavior(const Behavior& behavior);

    /// @brief Generate behavior name from condition
    /// @param condition Condition expression
    /// @return Human-readable behavior name
    ///
    /// Examples:
    /// - p == nullptr → "null_ptr"
    /// - x > 0 → "positive"
    /// - b == 0 → "zero_divisor"
    std::string generateBehaviorName(const clang::Expr* condition);

    /// @brief Format behaviors as ACSL annotation
    /// @param behaviors Vector of behaviors
    /// @param isComplete Whether behaviors are complete
    /// @param isDisjoint Whether behaviors are disjoint
    /// @return Formatted ACSL behavior annotation
    std::string formatBehaviors(const std::vector<Behavior>& behaviors,
                                 bool isComplete,
                                 bool isDisjoint);

private:
    /// @brief Helper: Convert C++ expression to ACSL syntax
    /// @param expr C++ expression from AST
    /// @return ACSL expression string
    std::string convertExprToACSL(const clang::Expr* expr);

    /// @brief Helper: Check if two conditions overlap
    /// @param cond1 First condition
    /// @param cond2 Second condition
    /// @return true if conditions can both be true simultaneously
    bool conditionsOverlap(const clang::Expr* cond1, const clang::Expr* cond2);

    /// @brief Helper: Check if conditions cover all cases
    /// @param conditions Vector of all condition expressions
    /// @return true if conditions are exhaustive
    bool conditionsAreExhaustive(const std::vector<const clang::Expr*>& conditions);

    /// @brief Helper: Extract return statement from if branch
    /// @param ifStmt If statement to analyze
    /// @return Return statement if found, nullptr otherwise
    const clang::ReturnStmt* extractReturnFromBranch(const clang::IfStmt* ifStmt);

    /// @brief Helper: Check if expression is null check
    /// @param expr Expression to analyze
    /// @return true if this is a null pointer check
    bool isNullCheck(const clang::Expr* expr);

    /// @brief Helper: Check if expression is range check
    /// @param expr Expression to analyze
    /// @return true if this is a value range check
    bool isRangeCheck(const clang::Expr* expr);
};

#endif // ACSL_BEHAVIOR_ANNOTATOR_H
