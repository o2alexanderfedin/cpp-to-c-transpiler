#ifndef ACSL_MEMORY_PREDICATE_ANALYZER_H
#define ACSL_MEMORY_PREDICATE_ANALYZER_H

// Phase 6: Advanced Memory Predicates (v1.23.0)
// Epic #193: ACSL Annotation Generation for Transpiled Code
//
// SOLID Principles:
// - Single Responsibility: Analyzes and generates memory-related ACSL predicates only
// - Open/Closed: Can be extended with new memory predicate types
// - Liskov Substitution: Compatible with ACSL generator hierarchy
// - Interface Segregation: Focused interface for memory predicate analysis
// - Dependency Inversion: Depends on Clang AST abstractions, not concrete implementations

#include "ACSLGenerator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include <string>
#include <vector>
#include <memory>

/// @brief Generates advanced ACSL memory predicates for memory safety verification
///
/// Supports ACSL memory predicates:
/// - \\allocable(size) - Precondition for memory allocation
/// - \\freeable(ptr) - Precondition for memory deallocation
/// - \\block_length(ptr) - Size of allocated memory block
/// - \\base_addr(ptr) - Base address of memory block
/// - \\fresh(ptr, size) - Newly allocated, non-aliased memory
///
/// Memory lifecycle tracking:
/// - Allocation: malloc, calloc, new, custom allocators
/// - Deallocation: free, delete, custom deallocators
/// - Reallocation: realloc (combines free + alloc semantics)
/// - Pointer arithmetic: Ensures operations stay within block bounds
///
/// Safety properties verified:
/// - No double-free (freeable at most once)
/// - No use-after-free (not valid after free)
/// - No out-of-bounds access (offset < block_length)
/// - Fresh memory on allocation (non-aliasing)
///
/// ACSL format: Memory predicates in function contracts
/// Reference: https://frama-c.com/html/acsl.html (v1.23.0+)
class ACSLMemoryPredicateAnalyzer : public ACSLGenerator {
public:
    /// @brief Default constructor - inherits ACSL level from base
    ACSLMemoryPredicateAnalyzer();

    /// @brief Constructor with specific ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLMemoryPredicateAnalyzer(ACSLLevel level);

    /// @brief Constructor with ACSL level and output mode
    /// @param level ACSL coverage level (Basic or Full)
    /// @param mode Output mode (Inline or Separate)
    ACSLMemoryPredicateAnalyzer(ACSLLevel level, ACSLOutputMode mode);

    /// @brief Generate memory predicates for a function
    /// @param func Function declaration to analyze
    /// @return ACSL contract with memory predicates (or empty if no memory operations)
    ///
    /// Example for malloc:
    /// /*@
    ///   requires \\allocable(size);
    ///   requires size >= 0;
    ///   ensures \\valid(\\result) || \\result == \\null;
    ///   ensures \\fresh(\\result, size);
    ///   ensures \\block_length(\\result) == size;
    /// */
    std::string generateMemoryPredicates(const clang::FunctionDecl* func);

    /// @brief Check if function performs memory allocation
    /// @param func Function declaration
    /// @return true if function allocates memory
    bool isAllocationFunction(const clang::FunctionDecl* func) const;

    /// @brief Check if function performs memory deallocation
    /// @param func Function declaration
    /// @return true if function deallocates memory
    bool isDeallocationFunction(const clang::FunctionDecl* func) const;

    /// @brief Check if function performs memory reallocation
    /// @param func Function declaration
    /// @return true if function reallocates memory
    bool isReallocationFunction(const clang::FunctionDecl* func) const;

    /// @brief Check if function performs pointer arithmetic
    /// @param func Function declaration
    /// @return true if function has pointer arithmetic operations
    bool hasPointerArithmetic(const clang::FunctionDecl* func) const;

    /// @brief Check if function computes base addresses
    /// @param func Function declaration
    /// @return true if function computes base addresses from pointers
    bool computesBaseAddress(const clang::FunctionDecl* func) const;

protected:
    /// @brief Generate allocable precondition for allocation functions
    /// @param func Function declaration
    /// @return requires \\allocable(size) clause (or empty)
    std::string generateAllocablePrecondition(const clang::FunctionDecl* func);

    /// @brief Generate freeable precondition for deallocation functions
    /// @param func Function declaration
    /// @return requires \\freeable(ptr) clause (or empty)
    std::string generateFreeablePrecondition(const clang::FunctionDecl* func);

    /// @brief Generate block_length postcondition for allocations
    /// @param func Function declaration
    /// @return ensures \\block_length(\\result) == size clause (or empty)
    std::string generateBlockLengthPostcondition(const clang::FunctionDecl* func);

    /// @brief Generate base_addr postcondition for base address computations
    /// @param func Function declaration
    /// @return ensures clause with \\base_addr (or empty)
    std::string generateBaseAddrPostcondition(const clang::FunctionDecl* func);

    /// @brief Generate fresh memory postcondition for allocations
    /// @param func Function declaration
    /// @return ensures \\fresh(\\result, size) clause (or empty)
    std::string generateFreshPostcondition(const clang::FunctionDecl* func);

    /// @brief Generate validity postcondition after free
    /// @param func Function declaration
    /// @return ensures !\\valid(ptr) clause (or empty)
    std::string generateInvalidAfterFreePostcondition(const clang::FunctionDecl* func);

    /// @brief Generate pointer arithmetic safety preconditions
    /// @param func Function declaration
    /// @return requires offset < \\block_length(ptr) clause (or empty)
    std::string generatePointerArithmeticSafety(const clang::FunctionDecl* func);

    /// @brief Detect size parameter for allocation functions
    /// @param func Function declaration
    /// @return Size parameter, or nullptr if not found
    const clang::ParmVarDecl* detectSizeParameter(const clang::FunctionDecl* func) const;

    /// @brief Detect pointer parameter for deallocation functions
    /// @param func Function declaration
    /// @return Pointer parameter, or nullptr if not found
    const clang::ParmVarDecl* detectPointerParameter(const clang::FunctionDecl* func) const;

    /// @brief Detect offset parameter for pointer arithmetic
    /// @param func Function declaration
    /// @return Offset parameter, or nullptr if not found
    const clang::ParmVarDecl* detectOffsetParameter(const clang::FunctionDecl* func) const;

    /// @brief Check if function name suggests allocation
    /// @param funcName Function name
    /// @return true if name suggests allocation (malloc, alloc, create, new, make)
    bool isAllocationName(const std::string& funcName) const;

    /// @brief Check if function name suggests deallocation
    /// @param funcName Function name
    /// @return true if name suggests deallocation (free, delete, release, destroy)
    bool isDeallocationName(const std::string& funcName) const;

    /// @brief Check if function name suggests reallocation
    /// @param funcName Function name
    /// @return true if name suggests reallocation (realloc, resize, expand)
    bool isReallocationName(const std::string& funcName) const;

    /// @brief Check if function name suggests pointer offset
    /// @param funcName Function name
    /// @return true if name suggests pointer offset (offset, advance, next, prev)
    bool isOffsetName(const std::string& funcName) const;

    /// @brief Check if function name suggests base address computation
    /// @param funcName Function name
    /// @return true if name suggests base address (base, align, round)
    bool isBaseAddrName(const std::string& funcName) const;

private:
    /// @brief Analyze function body for malloc/calloc/new calls
    /// @param func Function declaration
    /// @return true if body contains allocation calls
    bool bodyContainsAllocation(const clang::FunctionDecl* func) const;

    /// @brief Analyze function body for free/delete calls
    /// @param func Function declaration
    /// @return true if body contains deallocation calls
    bool bodyContainsDeallocation(const clang::FunctionDecl* func) const;

    /// @brief Analyze function body for realloc calls
    /// @param func Function declaration
    /// @return true if body contains reallocation calls
    bool bodyContainsReallocation(const clang::FunctionDecl* func) const;

    /// @brief Find parameter by name pattern
    /// @param func Function declaration
    /// @param namePattern Parameter name pattern to match
    /// @return Matching parameter, or nullptr
    const clang::ParmVarDecl* findParameterByPattern(
        const clang::FunctionDecl* func,
        const std::vector<std::string>& namePattern) const;
};

#endif // ACSL_MEMORY_PREDICATE_ANALYZER_H
