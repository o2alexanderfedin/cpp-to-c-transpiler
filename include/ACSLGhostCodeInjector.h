#ifndef ACSL_GHOST_CODE_INJECTOR_H
#define ACSL_GHOST_CODE_INJECTOR_H

// Phase 4 (v1.21.0): ACSL Ghost Code Injection
// Roadmap: .planning/ROADMAP.md
// Plan: .planning/phases/04-ghost-code/PLAN.md
//
// SOLID Principles:
// - Single Responsibility: Generates ACSL ghost code only (variables, assignments, blocks)
// - Open/Closed: Extends ACSLGenerator base class
// - Liskov Substitution: Can substitute ACSLGenerator where needed
// - Interface Segregation: Focused interface for ghost code generation
// - Dependency Inversion: Depends on Clang AST abstractions

#include "ACSLGenerator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>

/// @brief Generates ACSL ghost code for proof-relevant values
///
/// Produces ghost variables, assignments, and blocks for specification purposes:
/// - Ghost variable declarations: Values not in original code but needed for proofs
/// - Ghost assignments: Maintain ghost variable values throughout execution
/// - Ghost blocks: Multi-statement ghost logic
/// - Integration with loop invariants and assertions
///
/// Ghost code characteristics:
/// - Comment-only (no runtime impact)
/// - Track proof-relevant state (max seen, sum, count, previous values)
/// - Enable more precise invariants and assertions
/// - Support verification without modifying runtime behavior
///
/// ACSL ghost code syntax:
/// - Declaration: //@ ghost type variable_name = initial_value;
/// - Assignment: //@ ghost variable_name = new_value;
/// - Block: //@ ghost { type var = value; /* statements */ }
///
/// Common use cases:
/// - Max/min tracking: //@ ghost int max_seen = arr[0];
/// - Sum tracking: //@ ghost int sum = 0;
/// - Counter: //@ ghost int count = 0;
/// - Previous value: //@ ghost int old_val = val;
/// - Array copy: //@ ghost int copy[n];
///
/// ACSL Reference: https://frama-c.com/html/acsl.html (v1.22+)
class ACSLGhostCodeInjector : public ACSLGenerator {
public:
    /// @brief Default constructor - inherits ACSL level from base
    ACSLGhostCodeInjector();

    /// @brief Constructor with specific ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLGhostCodeInjector(ACSLLevel level);

    /// @brief Constructor with ACSL level and output mode
    /// @param level ACSL coverage level (Basic or Full)
    /// @param mode Output mode (Inline or Separate)
    ACSLGhostCodeInjector(ACSLLevel level, ACSLOutputMode mode);

    /// @brief Inject ghost code into a function
    /// @param func Function to analyze and inject ghost code
    /// @return Generated ghost code as ACSL comments
    ///
    /// Example output:
    /// //@ ghost int max_seen = arr[0];
    /// for (int i = 1; i < size; i++) {
    ///   //@ ghost if (arr[i] > max_seen) max_seen = arr[i];
    ///   if (arr[i] > max) max = arr[i];
    /// }
    std::string injectGhostCode(const clang::FunctionDecl* func);

private:
    /// @brief Purpose of ghost variable
    enum class GhostPurpose {
        MaxTracking,        ///< Track maximum value seen
        MinTracking,        ///< Track minimum value seen
        SumTracking,        ///< Track accumulator sum
        CountTracking,      ///< Track occurrence counter
        PreviousValue,      ///< Track value before update
        ArrayCopy,          ///< Track array snapshot
        InvariantHelper,    ///< Help express loop invariant
        AssertionHelper,    ///< Help express assertion
        Custom              ///< Custom purpose
    };

    /// @brief Ghost variable specification
    struct GhostVariable {
        std::string name;           ///< Ghost variable name
        std::string type;           ///< Type (int, integer, etc.)
        std::string initialValue;   ///< Initial value expression
        const clang::Stmt* scope;   ///< Scope where ghost var lives
        GhostPurpose purpose;       ///< Why this ghost var exists

        GhostVariable() : scope(nullptr), purpose(GhostPurpose::Custom) {}

        GhostVariable(const std::string& n, const std::string& t,
                     const std::string& init, const clang::Stmt* s, GhostPurpose p)
            : name(n), type(t), initialValue(init), scope(s), purpose(p) {}
    };

protected:
    /// @brief Analyze function for ghost variable opportunities
    /// @param func Function to analyze
    /// @return Vector of ghost variable opportunities
    ///
    /// Identifies places where ghost variables would help proofs:
    /// - Loop accumulators (sum, count)
    /// - Max/min tracking
    /// - Previous values before updates
    /// - Array snapshots
    std::vector<GhostVariable> analyzeGhostOpportunities(const clang::FunctionDecl* func);

    /// @brief Generate ghost variable declaration
    /// @param ghostVar Ghost variable specification
    /// @return ACSL ghost declaration
    ///
    /// Example: //@ ghost int max_seen = arr[0];
    std::string generateGhostDeclaration(const GhostVariable& ghostVar);

    /// @brief Generate ghost assignment statement
    /// @param ghostVar Ghost variable to update
    /// @param newValue New value expression
    /// @return ACSL ghost assignment
    ///
    /// Example: //@ ghost max_seen = arr[i];
    std::string generateGhostAssignment(const GhostVariable& ghostVar,
                                        const std::string& newValue);

    /// @brief Generate ghost block for multi-statement logic
    /// @param statements Vector of ghost statements
    /// @return ACSL ghost block
    ///
    /// Example:
    /// //@ ghost {
    /// //@   int old_val = val;
    /// //@   int new_val = val + 1;
    /// //@ }
    std::string generateGhostBlock(const std::vector<std::string>& statements);

    /// @brief Track ghost variable scope and lifetime
    /// @param ghostVar Ghost variable to track
    /// @param scope Scope (function, loop, block)
    void trackGhostVariable(const GhostVariable& ghostVar, const clang::Stmt* scope);

    /// @brief Check if ghost variable is in scope
    /// @param name Ghost variable name
    /// @param stmt Current statement
    /// @return true if ghost variable is accessible
    bool isGhostVariableInScope(const std::string& name, const clang::Stmt* stmt);

private:
    /// @brief AST visitor for ghost code analysis
    class GhostAnalysisVisitor : public clang::RecursiveASTVisitor<GhostAnalysisVisitor> {
    public:
        explicit GhostAnalysisVisitor(ACSLGhostCodeInjector* injector)
            : m_injector(injector) {}

        /// @brief Visit loops to identify accumulator patterns
        bool VisitForStmt(clang::ForStmt* stmt);

        /// @brief Visit loops to identify accumulator patterns
        bool VisitWhileStmt(clang::WhileStmt* stmt);

        /// @brief Visit assignments to track value changes
        bool VisitBinaryOperator(clang::BinaryOperator* op);

        /// @brief Visit variable declarations for tracking
        bool VisitVarDecl(clang::VarDecl* decl);

        /// @brief Visit array subscripts for copy tracking
        bool VisitArraySubscriptExpr(clang::ArraySubscriptExpr* expr);

        /// @brief Get collected ghost opportunities
        const std::vector<GhostVariable>& getGhostVariables() const {
            return m_ghostVariables;
        }

    private:
        ACSLGhostCodeInjector* m_injector;
        std::vector<GhostVariable> m_ghostVariables;
    };

    /// @brief Detect max tracking pattern
    /// @param stmt Statement to analyze
    /// @return Ghost variable if pattern detected, nullptr otherwise
    GhostVariable* detectMaxTracking(const clang::Stmt* stmt);

    /// @brief Detect min tracking pattern
    /// @param stmt Statement to analyze
    /// @return Ghost variable if pattern detected, nullptr otherwise
    GhostVariable* detectMinTracking(const clang::Stmt* stmt);

    /// @brief Detect sum accumulation pattern
    /// @param stmt Statement to analyze
    /// @return Ghost variable if pattern detected, nullptr otherwise
    GhostVariable* detectSumTracking(const clang::Stmt* stmt);

    /// @brief Detect counter increment pattern
    /// @param stmt Statement to analyze
    /// @return Ghost variable if pattern detected, nullptr otherwise
    GhostVariable* detectCountTracking(const clang::Stmt* stmt);

    /// @brief Detect value mutation requiring previous value
    /// @param stmt Statement to analyze
    /// @return Ghost variable if pattern detected, nullptr otherwise
    GhostVariable* detectPreviousValueTracking(const clang::Stmt* stmt);

    /// @brief Detect array modification requiring snapshot
    /// @param stmt Statement to analyze
    /// @return Ghost variable if pattern detected, nullptr otherwise
    GhostVariable* detectArrayCopyTracking(const clang::Stmt* stmt);

    /// @brief Get ACSL type from C++ type
    /// @param type C++ QualType
    /// @return ACSL type string (integer, real, boolean)
    std::string getACSLType(clang::QualType type);

    /// @brief Convert C++ expression to ACSL logic expression
    /// @param expr Clang expression
    /// @return ACSL logic expression string
    std::string convertToACSLExpr(const clang::Expr* expr);

    /// @brief Check if ghost variable name is unique
    /// @param name Proposed ghost variable name
    /// @return Unique name (may append suffix if conflict)
    std::string ensureUniqueName(const std::string& name);

    /// @brief Format ghost code with proper indentation
    /// @param code Ghost code content
    /// @param indent Indentation level
    /// @return Formatted ghost code
    std::string formatGhostCode(const std::string& code, unsigned indent);

    /// @brief Map of declared ghost variables (name -> GhostVariable)
    std::unordered_map<std::string, GhostVariable> m_declaredGhostVars;

    /// @brief Set of ghost variable names in use
    std::unordered_set<std::string> m_ghostVarNames;

    /// @brief Counter for generating unique ghost names
    unsigned m_ghostVarCounter;

    friend class GhostAnalysisVisitor;
};

#endif // ACSL_GHOST_CODE_INJECTOR_H
