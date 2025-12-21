#ifndef ACSL_STATEMENT_ANNOTATOR_H
#define ACSL_STATEMENT_ANNOTATOR_H

// Phase 1 (v1.18.0): ACSL Statement Annotations
// Roadmap: .planning/ROADMAP.md
// Plan: .planning/phases/01-statement-annotations/PLAN.md
//
// SOLID Principles:
// - Single Responsibility: Generates ACSL statement annotations only (assert, assume, check)
// - Open/Closed: Extends ACSLGenerator base class
// - Liskov Substitution: Can substitute ACSLGenerator where needed
// - Interface Segregation: Focused interface for statement annotation generation
// - Dependency Inversion: Depends on Clang AST abstractions

#include "ACSLGenerator.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include <string>
#include <vector>
#include <memory>

/// @brief Annotation verbosity level for statement annotations
enum class AnnotationLevel {
    None,   ///< No statement annotations
    Basic,  ///< Essential safety checks (null pointers, division by zero, array bounds)
    Full    ///< Comprehensive annotations (basic + buffer overflow, arithmetic overflow, casts, custom checks)
};

/// @brief Generates ACSL statement annotations within function bodies
///
/// Produces statement-level ACSL annotations at safety-critical points:
/// - assert: Runtime + proof obligations (pointer validity, array bounds, division by zero)
/// - assume: Proof context assumptions (post-validation, constructors, platform)
/// - check: Proof milestones only (algorithm invariants, proof obligations)
///
/// Strategic placement:
/// - Before pointer dereferences: //@ assert \valid(p);
/// - Before array accesses: //@ assert 0 <= idx < size;
/// - Before divisions: //@ assert divisor != 0;
/// - Before buffer operations: //@ assert strlen(src) < buffer_size;
/// - After validation: //@ assume 0 <= validated_input <= 100;
/// - At proof milestones: //@ check \forall integer i; ...
///
/// ACSL format: Statement annotations appear inline before statements
/// Reference: https://frama-c.com/html/acsl.html (v1.22+)
class ACSLStatementAnnotator : public ACSLGenerator {
public:
    /// @brief Default constructor - Basic ACSL level, Inline output mode
    ACSLStatementAnnotator();

    /// @brief Constructor with specific ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLStatementAnnotator(ACSLLevel level);

    /// @brief Constructor with ACSL level and output mode
    /// @param level ACSL coverage level (Basic or Full)
    /// @param mode Output mode (Inline or Separate)
    ACSLStatementAnnotator(ACSLLevel level, ACSLOutputMode mode);

    /// @brief Annotate statements within a function
    /// @param func Function to annotate
    /// @param level Statement annotation verbosity level
    /// @return Annotated source code with statement annotations
    ///
    /// Example output:
    /// void process(int *ptr, int idx, int size) {
    ///   //@ assert \valid(ptr);
    ///   //@ assert 0 <= idx < size;
    ///   ptr[idx] = 0;
    /// }
    std::string annotateFunction(const clang::FunctionDecl *func,
                                  AnnotationLevel level);

private:
    /// @brief AST visitor for statement traversal and annotation
    class StatementVisitor : public clang::RecursiveASTVisitor<StatementVisitor> {
    public:
        explicit StatementVisitor(ACSLStatementAnnotator* annotator, AnnotationLevel level)
            : m_annotator(annotator), m_level(level) {}

        /// @brief Visit statement and collect annotations
        bool VisitStmt(clang::Stmt* stmt);

        /// @brief Get collected annotations
        const std::vector<std::pair<const clang::Stmt*, std::string>>& getAnnotations() const {
            return m_annotations;
        }

    private:
        ACSLStatementAnnotator* m_annotator;
        AnnotationLevel m_level;
        std::vector<std::pair<const clang::Stmt*, std::string>> m_annotations;
    };

    /// @brief Generate assert annotation for expression
    /// @param expr Expression to assert
    /// @return ACSL assert annotation string (e.g., "//@ assert \valid(ptr);")
    std::string generateAssert(const clang::Expr *expr);

    /// @brief Generate assume annotation for expression
    /// @param expr Expression to assume
    /// @return ACSL assume annotation string (e.g., "//@ assume x > 0;")
    std::string generateAssume(const clang::Expr *expr);

    /// @brief Generate check annotation for expression
    /// @param expr Expression to check
    /// @return ACSL check annotation string (e.g., "//@ check \forall integer i; ...")
    std::string generateCheck(const clang::Expr *expr);

    /// @brief Determine if statement needs annotation
    /// @param stmt Statement to analyze
    /// @param level Annotation verbosity level
    /// @return true if statement requires annotation at this level
    bool needsAnnotation(const clang::Stmt *stmt, AnnotationLevel level);

    /// @brief Extract safety property from statement
    /// @param stmt Statement to analyze
    /// @return ACSL safety property string
    std::string extractSafetyProperty(const clang::Stmt *stmt);

    /// @brief Detect if expression is a pointer dereference
    /// @param expr Expression to analyze
    /// @return Pointer being dereferenced, or nullptr
    const clang::Expr* detectPointerDereference(const clang::Expr *expr);

    /// @brief Detect if expression is an array access
    /// @param expr Expression to analyze
    /// @return ArraySubscriptExpr, or nullptr
    const clang::ArraySubscriptExpr* detectArrayAccess(const clang::Expr *expr);

    /// @brief Detect if expression is a division operation
    /// @param expr Expression to analyze
    /// @return BinaryOperator for division, or nullptr
    const clang::BinaryOperator* detectDivisionOperation(const clang::Expr *expr);

    /// @brief Detect if expression is a cast operation
    /// @param expr Expression to analyze
    /// @return CastExpr, or nullptr
    const clang::CastExpr* detectCastOperation(const clang::Expr *expr);

    /// @brief Detect if statement contains buffer operation
    /// @param stmt Statement to analyze
    /// @return true if statement contains strcpy, strcat, memcpy, etc.
    bool detectBufferOperation(const clang::Stmt *stmt);

    /// @brief Extract pointer validity constraint
    /// @param ptrExpr Pointer expression
    /// @return ACSL validity constraint (e.g., "\\valid(ptr)")
    std::string extractPointerValidity(const clang::Expr *ptrExpr);

    /// @brief Extract array bounds constraint
    /// @param arrayExpr Array subscript expression
    /// @return ACSL bounds constraint (e.g., "0 <= idx < size")
    std::string extractArrayBounds(const clang::ArraySubscriptExpr *arrayExpr);

    /// @brief Extract non-zero constraint for division
    /// @param divisor Divisor expression
    /// @return ACSL non-zero constraint (e.g., "divisor != 0")
    std::string extractNonZeroConstraint(const clang::Expr *divisor);

    /// @brief Extract buffer size constraint
    /// @param stmt Statement containing buffer operation
    /// @return ACSL buffer constraint (e.g., "strlen(src) < buffer_size")
    std::string extractBufferConstraint(const clang::Stmt *stmt);

    /// @brief Extract type safety constraint for cast
    /// @param castExpr Cast expression
    /// @return ACSL cast safety constraint
    std::string extractCastConstraint(const clang::CastExpr *castExpr);

    /// @brief Check if validation precedes this point
    /// @param stmt Statement to analyze
    /// @return true if preceding statements validate inputs
    bool hasValidationContext(const clang::Stmt *stmt);

    /// @brief Check if this is a constructor initialization
    /// @param stmt Statement to analyze
    /// @return true if in constructor body after initialization
    bool isConstructorPostInit(const clang::Stmt *stmt);

    /// @brief Generate assume annotation for validated input
    /// @param stmt Statement after validation
    /// @return ACSL assume annotation
    std::string generateValidatedAssumption(const clang::Stmt *stmt);

    /// @brief Generate assume annotation for constructor
    /// @param stmt Statement in constructor
    /// @return ACSL assume annotation
    std::string generateConstructorAssumption(const clang::Stmt *stmt);

    /// @brief Check if statement is a proof milestone
    /// @param stmt Statement to analyze
    /// @return true if statement represents proof milestone
    bool isProofMilestone(const clang::Stmt *stmt);

    /// @brief Generate check annotation for proof milestone
    /// @param stmt Proof milestone statement
    /// @return ACSL check annotation
    std::string generateProofMilestoneCheck(const clang::Stmt *stmt);

    /// @brief Check if statement maintains invariant
    /// @param stmt Statement to analyze
    /// @return true if statement should preserve invariant
    bool maintainsInvariant(const clang::Stmt *stmt);

    /// @brief Generate check annotation for invariant maintenance
    /// @param stmt Statement maintaining invariant
    /// @return ACSL check annotation
    std::string generateInvariantMaintenanceCheck(const clang::Stmt *stmt);

    /// @brief Get expression being evaluated in statement
    /// @param stmt Statement to analyze
    /// @return Expression, or nullptr
    const clang::Expr* getStatementExpression(const clang::Stmt *stmt);

    /// @brief Format annotation with proper indentation
    /// @param annotation ACSL annotation content
    /// @param stmt Statement the annotation precedes
    /// @return Formatted annotation string
    std::string formatAnnotation(const std::string& annotation, const clang::Stmt *stmt);

    friend class StatementVisitor;
};

#endif // ACSL_STATEMENT_ANNOTATOR_H
