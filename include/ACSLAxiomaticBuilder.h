#ifndef ACSL_AXIOMATIC_BUILDER_H
#define ACSL_AXIOMATIC_BUILDER_H

// Phase 3 (v1.20.0): ACSL Axiomatic Definitions
// Roadmap: .planning/ROADMAP.md
// Plan: .planning/phases/03-axiomatic-definitions/PLAN.md
//
// SOLID Principles:
// - Single Responsibility: Generates ACSL axiomatic blocks only
// - Open/Closed: Extends ACSLGenerator base class
// - Liskov Substitution: Can substitute ACSLGenerator where needed
// - Interface Segregation: Focused interface for axiomatic generation
// - Dependency Inversion: Depends on Clang AST abstractions

#include "ACSLGenerator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include <string>
#include <vector>
#include <unordered_set>
#include <unordered_map>

/// @brief Generates ACSL axiomatic blocks (logic functions, axioms, lemmas)
///
/// Produces axiomatic definitions that abstract mathematical properties:
/// - Logic functions: Pure function abstractions
/// - Axioms: Fundamental properties (commutativity, positivity, etc.)
/// - Lemmas: Derived properties provable from axioms
/// - Inductive predicates: Recursive definitions
///
/// Example axiomatic block:
/// /*@ axiomatic IntMath {
///   @   logic integer abs(integer x) =
///   @     x >= 0 ? x : -x;
///   @
///   @   axiom abs_positive:
///   @     \forall integer x; abs(x) >= 0;
///   @
///   @   lemma abs_zero:
///   @     \forall integer x; abs(x) == 0 <==> x == 0;
///   @ }
///   @*/
///
/// ACSL Reference: https://frama-c.com/html/acsl.html (v1.22+)
class ACSLAxiomaticBuilder : public ACSLGenerator {
public:
    /// @brief Default constructor - inherits ACSL level from base
    ACSLAxiomaticBuilder();

    /// @brief Constructor with specific ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLAxiomaticBuilder(ACSLLevel level);

    /// @brief Constructor with ACSL level and output mode
    /// @param level ACSL coverage level (Basic or Full)
    /// @param mode Output mode (Inline or Separate)
    ACSLAxiomaticBuilder(ACSLLevel level, ACSLOutputMode mode);

    /// @brief Generate complete axiomatic block for a function
    /// @param func Function to analyze and generate axiomatics for
    /// @return Complete ACSL axiomatic block as formatted comment
    ///
    /// Example output:
    /// /*@ axiomatic AbsValue {
    ///   @   logic integer abs_value(integer x) =
    ///   @     x >= 0 ? x : -x;
    ///   @
    ///   @   axiom abs_positive:
    ///   @     \forall integer x; abs_value(x) >= 0;
    ///   @ }
    ///   @*/
    std::string generateAxiomaticBlock(const clang::FunctionDecl* func);

    /// @brief Generate axiomatic block for multiple related functions
    /// @param functions Vector of related functions (e.g., math library)
    /// @param blockName Name for the axiomatic block
    /// @return Combined axiomatic block
    std::string generateAxiomaticBlock(const std::vector<const clang::FunctionDecl*>& functions,
                                       const std::string& blockName);

protected:
    /// @brief Check if function is pure (suitable for logic abstraction)
    /// @param func Function to analyze
    /// @return true if function is pure (no side effects, deterministic)
    bool isPureFunction(const clang::FunctionDecl* func);

    /// @brief Generate logic function declaration from C function
    /// @param func Function to convert
    /// @return ACSL logic function declaration
    ///
    /// Converts:
    /// int abs_value(int x) { return (x >= 0) ? x : -x; }
    /// To:
    /// logic integer abs_value(integer x) = x >= 0 ? x : -x;
    std::string generateLogicFunction(const clang::FunctionDecl* func);

    /// @brief Detect and generate axioms for function properties
    /// @param func Function to analyze
    /// @return Vector of axiom declarations
    ///
    /// Detects properties like:
    /// - Commutativity: f(a, b) == f(b, a)
    /// - Associativity: f(f(a, b), c) == f(a, f(b, c))
    /// - Identity: f(x, 0) == x
    /// - Positivity: f(x) >= 0
    std::vector<std::string> generateAxioms(const clang::FunctionDecl* func);

    /// @brief Generate lemmas (derived properties) for function
    /// @param func Function to analyze
    /// @return Vector of lemma declarations
    ///
    /// Generates provable properties like:
    /// - abs(x) == 0 <==> x == 0
    /// - gcd(a, b) == gcd(b, a)
    std::vector<std::string> generateLemmas(const clang::FunctionDecl* func);

    /// @brief Generate inductive predicate from boolean function
    /// @param func Boolean-returning function
    /// @return Inductive predicate definition
    ///
    /// Example:
    /// bool is_sorted(int arr[], int size) →
    /// inductive sorted{L}(int *a, integer n) { ... }
    std::string generateInductivePredicate(const clang::FunctionDecl* func);

private:
    /// @brief Detect commutative property (f(a,b) == f(b,a))
    /// @param func Function to analyze
    /// @return true if function is commutative
    bool isCommutative(const clang::FunctionDecl* func);

    /// @brief Detect associative property (f(f(a,b),c) == f(a,f(b,c)))
    /// @param func Function to analyze
    /// @return true if function is associative
    bool isAssociative(const clang::FunctionDecl* func);

    /// @brief Detect identity element (f(x, id) == x)
    /// @param func Function to analyze
    /// @return Identity element value if exists, empty string otherwise
    std::string getIdentityElement(const clang::FunctionDecl* func);

    /// @brief Detect inverse operation (f(f_inv(x)) == id)
    /// @param func Function to analyze
    /// @return true if function has inverse property
    bool hasInverseProperty(const clang::FunctionDecl* func);

    /// @brief Detect distributive property over another operation
    /// @param func Function to analyze
    /// @return true if function is distributive
    bool isDistributive(const clang::FunctionDecl* func);

    /// @brief Detect positivity property (f(x) >= 0 for all x)
    /// @param func Function to analyze
    /// @return true if function always returns non-negative
    bool isAlwaysPositive(const clang::FunctionDecl* func);

    /// @brief Detect monotonicity property
    /// @param func Function to analyze
    /// @return true if function is monotonic
    bool isMonotonic(const clang::FunctionDecl* func);

    /// @brief Detect idempotent property (f(f(x)) == f(x))
    /// @param func Function to analyze
    /// @return true if function is idempotent
    bool isIdempotent(const clang::FunctionDecl* func);

    /// @brief Check axiom consistency (no contradictions)
    /// @param axioms Vector of axiom strings
    /// @return true if axioms are consistent
    ///
    /// Performs basic syntactic checks for obvious contradictions.
    /// Full semantic consistency requires SMT solver (future work).
    bool checkAxiomConsistency(const std::vector<std::string>& axioms);

    /// @brief Convert C type to ACSL logic type
    /// @param type C type
    /// @return ACSL logic type (integer, real, boolean)
    std::string convertToLogicType(clang::QualType type);

    /// @brief Convert C expression to ACSL logic expression
    /// @param expr C expression
    /// @return ACSL logic expression
    std::string convertToLogicExpr(const clang::Expr* expr);

    /// @brief Analyze function body for properties
    /// @param func Function to analyze
    /// @return Detected properties (commutativity, associativity, etc.)
    std::unordered_set<std::string> analyzeProperties(const clang::FunctionDecl* func);

    /// @brief Get axiomatic block name from function
    /// @param func Function
    /// @return Block name (e.g., "AbsValue", "IntMath")
    std::string getAxiomaticBlockName(const clang::FunctionDecl* func);

    /// @brief Get axiomatic block name for multiple functions
    /// @param functions Vector of functions
    /// @return Block name
    std::string getAxiomaticBlockName(const std::vector<const clang::FunctionDecl*>& functions);

    /// @brief Format axiomatic block with proper indentation
    /// @param blockName Name of axiomatic block
    /// @param logicFunctions Vector of logic function declarations
    /// @param axioms Vector of axiom declarations
    /// @param lemmas Vector of lemma declarations
    /// @return Formatted axiomatic block
    std::string formatAxiomaticBlock(const std::string& blockName,
                                     const std::vector<std::string>& logicFunctions,
                                     const std::vector<std::string>& axioms,
                                     const std::vector<std::string>& lemmas);

    /// @brief Check if function is recursive
    /// @param func Function to check
    /// @return true if function calls itself
    bool isRecursive(const clang::FunctionDecl* func);

    /// @brief Check if function is template or template specialization
    /// @param func Function to check
    /// @return true if function is template-based
    bool isTemplate(const clang::FunctionDecl* func);

    /// @brief Extract function body as string
    /// @param func Function
    /// @return Body as string (for conversion to logic expression)
    std::string extractFunctionBody(const clang::FunctionDecl* func);

    /// @brief Generate axiom for commutativity
    /// @param func Commutative function
    /// @return Axiom string
    std::string generateCommutativityAxiom(const clang::FunctionDecl* func);

    /// @brief Generate axiom for associativity
    /// @param func Associative function
    /// @return Axiom string
    std::string generateAssociativityAxiom(const clang::FunctionDecl* func);

    /// @brief Generate axiom for identity element
    /// @param func Function with identity
    /// @param identity Identity element value
    /// @return Axiom string
    std::string generateIdentityAxiom(const clang::FunctionDecl* func,
                                      const std::string& identity);

    /// @brief Generate axiom for inverse property
    /// @param func Function with inverse
    /// @return Axiom string
    std::string generateInverseAxiom(const clang::FunctionDecl* func);

    /// @brief Generate axiom for distributivity
    /// @param func Distributive function
    /// @return Axiom string
    std::string generateDistributivityAxiom(const clang::FunctionDecl* func);

    /// @brief Generate axiom for positivity
    /// @param func Always-positive function
    /// @return Axiom string
    std::string generatePositivityAxiom(const clang::FunctionDecl* func);

    /// @brief Set of functions being processed (for recursion detection)
    std::unordered_set<const clang::FunctionDecl*> m_processingFunctions;

    /// @brief Cache of generated logic functions (avoid duplicates)
    std::unordered_map<std::string, std::string> m_logicFunctionCache;
};

#endif // ACSL_AXIOMATIC_BUILDER_H
