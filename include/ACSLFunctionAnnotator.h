#ifndef ACSL_FUNCTION_ANNOTATOR_H
#define ACSL_FUNCTION_ANNOTATOR_H

// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #196: Implement ACSLFunctionAnnotator for comprehensive function contracts
//
// SOLID Principles:
// - Single Responsibility: Generates ACSL function contracts only
// - Open/Closed: Extends ACSLGenerator base class
// - Liskov Substitution: Can substitute ACSLGenerator where needed
// - Interface Segregation: Focused interface for function contract generation
// - Dependency Inversion: Depends on Clang AST abstractions

#include "ACSLGenerator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include <string>
#include <vector>

/// @brief Generates comprehensive ACSL function contracts
///
/// Produces complete ACSL annotations including:
/// - requires clauses (pointer validity, value constraints, array bounds)
/// - ensures clauses (return values, postconditions, quantifiers)
/// - assigns clauses (side effect tracking, array ranges)
///
/// Supports advanced ACSL features:
/// - Universal quantification (\\forall)
/// - Existential quantification (\\exists)
/// - Old values (\\old())
/// - Pointer validity (\\valid, \\valid_read)
/// - Array bounds (\\valid(arr + (0..n-1)))
/// - Separation (\\separated(p1, p2))
/// - Fresh memory (\\fresh(\\result, size))
///
/// ACSL format: Function contracts appear before function declarations
/// Reference: https://frama-c.com/html/acsl.html (v1.22+)
class ACSLFunctionAnnotator : public ACSLGenerator {
public:
    /// @brief Default constructor - inherits ACSL level from base
    ACSLFunctionAnnotator();

    /// @brief Constructor with specific ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLFunctionAnnotator(ACSLLevel level);

    /// @brief Constructor with ACSL level and output mode
    /// @param level ACSL coverage level (Basic or Full)
    /// @param mode Output mode (Inline or Separate)
    ACSLFunctionAnnotator(ACSLLevel level, ACSLOutputMode mode);

    /// @brief Generate complete ACSL function contract
    /// @param func Function declaration to annotate
    /// @return Complete ACSL contract as formatted comment block
    ///
    /// Example output:
    /// /*@
    ///   requires \\valid(arr + (0..n-1));
    ///   requires n >= 0;
    ///   assigns arr[0..n-1];
    ///   ensures \\forall integer i; 0 <= i < n ==> arr[i] == value;
    /// */
    std::string generateFunctionContract(const clang::FunctionDecl* func);

    /// @brief Generate requires clauses (preconditions)
    /// @param func Function declaration
    /// @return Vector of requires clause strings (without "requires" keyword)
    ///
    /// Generated clauses:
    /// - Pointer validity: \\valid(ptr), \\valid_read(const_ptr)
    /// - Array bounds: \\valid(arr + (0..n-1))
    /// - Value constraints: x >= 0, 0 <= index < size
    /// - Separation: \\separated(p1, p2)
    std::vector<std::string> generateRequiresClauses(const clang::FunctionDecl* func);

    /// @brief Generate ensures clauses (postconditions)
    /// @param func Function declaration
    /// @return Vector of ensures clause strings (without "ensures" keyword)
    ///
    /// Generated clauses:
    /// - Return value properties: \\result >= 0
    /// - Return value validity: \\valid(\\result) || \\result == \\null
    /// - Quantified postconditions: \\forall integer i; ...
    /// - Old value relationships: *out == \\old(*in) + 1
    /// - Fresh memory: \\fresh(\\result, size)
    std::vector<std::string> generateEnsuresClauses(const clang::FunctionDecl* func);

    /// @brief Generate assigns clauses (side effects)
    /// @param func Function declaration
    /// @return Vector of assigns clause strings (locations modified)
    ///
    /// Generated clauses:
    /// - Pointer dereferences: *ptr
    /// - Array ranges: arr[0..n-1]
    /// - Struct fields: obj->field
    /// - Pure functions: \\nothing
    /// - Unknown side effects: \\everything (conservative)
    std::vector<std::string> generateAssignsClauses(const clang::FunctionDecl* func);

protected:
    /// @brief Analyze pointer parameter for validity contracts
    /// @param param Pointer parameter declaration
    /// @param sizeParam Optional size parameter for arrays (nullptr if none)
    /// @return Validity constraint string (e.g., "\\valid(ptr + (0..n-1))")
    std::string analyzePointerValidity(const clang::ParmVarDecl* param,
                                       const clang::ParmVarDecl* sizeParam = nullptr);

    /// @brief Infer value constraints from parameter type and name
    /// @param param Parameter declaration
    /// @return Value constraint string (e.g., "n >= 0", "0 <= index < size")
    std::string inferValueConstraints(const clang::ParmVarDecl* param);

    /// @brief Detect array-size parameter relationships
    /// @param func Function declaration
    /// @return Map of array parameter -> size parameter pairs
    std::vector<std::pair<const clang::ParmVarDecl*, const clang::ParmVarDecl*>>
    detectArraySizeRelationships(const clang::FunctionDecl* func);

    /// @brief Check if two pointer parameters should be separated
    /// @param p1 First pointer parameter
    /// @param p2 Second pointer parameter
    /// @return true if parameters are likely intended to be non-overlapping
    bool shouldBeSeparated(const clang::ParmVarDecl* p1, const clang::ParmVarDecl* p2);

    /// @brief Analyze function body for side effects
    /// @param func Function declaration
    /// @return Vector of memory locations modified
    std::vector<std::string> trackSideEffects(const clang::FunctionDecl* func);

    /// @brief Generate quantified postcondition from loop pattern
    /// @param func Function declaration
    /// @return Quantified postcondition string (or empty if not applicable)
    ///
    /// Detects patterns like:
    /// - Array initialization: for (i=0; i<n; i++) arr[i] = val;
    ///   → \\forall integer i; 0 <= i < n ==> arr[i] == val
    /// - Array search: for (i=0; i<n; i++) if (arr[i] == target) return i;
    ///   → \\exists integer i; 0 <= i < n && arr[i] == target
    std::string generateQuantifiedPostcondition(const clang::FunctionDecl* func);

    /// @brief Analyze return value for postconditions
    /// @param func Function declaration
    /// @return Ensures clause for return value (or empty if void/no inference)
    std::string analyzeReturnValue(const clang::FunctionDecl* func);

    /// @brief Check if function is pure (no side effects)
    /// @param func Function declaration
    /// @return true if function has no observable side effects
    bool isPureFunction(const clang::FunctionDecl* func);

    /// @brief Detect if function allocates memory
    /// @param func Function declaration
    /// @return true if function appears to allocate memory (new, malloc)
    bool allocatesMemory(const clang::FunctionDecl* func);

private:
    /// @brief Helper: Get parameter by name
    /// @param func Function declaration
    /// @param name Parameter name to search for
    /// @return Parameter declaration or nullptr if not found
    const clang::ParmVarDecl* getParameterByName(const clang::FunctionDecl* func,
                                                   const std::string& name);

    /// @brief Helper: Check if parameter is pointer type
    /// @param param Parameter declaration
    /// @return true if parameter is a pointer
    bool isPointerParameter(const clang::ParmVarDecl* param);

    /// @brief Helper: Check if parameter is const pointer
    /// @param param Parameter declaration
    /// @return true if parameter is const T* or T* const
    bool isConstPointer(const clang::ParmVarDecl* param);

    /// @brief Helper: Check if parameter name suggests it's a size/count
    /// @param param Parameter declaration
    /// @return true if name like "size", "count", "length", "n", etc.
    bool isSizeParameter(const clang::ParmVarDecl* param);

    /// @brief Helper: Check if parameter name suggests it's an index
    /// @param param Parameter declaration
    /// @return true if name like "index", "idx", "i", "pos", etc.
    bool isIndexParameter(const clang::ParmVarDecl* param);

    /// @brief Helper: Format assigns clause items into single string
    /// @param items Vector of individual assign locations
    /// @return Formatted assigns clause (e.g., "*ptr, arr[0..n-1]")
    std::string formatAssignsClause(const std::vector<std::string>& items);
};

#endif // ACSL_FUNCTION_ANNOTATOR_H
