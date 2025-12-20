#ifndef ACSL_CLASS_ANNOTATOR_H
#define ACSL_CLASS_ANNOTATOR_H

// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #198: ACSLClassAnnotator for class invariant predicates
//
// SOLID Principles:
// - Single Responsibility: Generates ACSL class invariant predicates only
// - Open/Closed: Extends ACSLGenerator base class
// - Liskov Substitution: Can substitute ACSLGenerator where needed
// - Interface Segregation: Focused interface for class invariant generation
// - Dependency Inversion: Depends on Clang AST abstractions

#include "ACSLGenerator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include <string>
#include <vector>

/// @brief Generates comprehensive ACSL class invariant predicates
///
/// Produces ACSL class invariants including:
/// - Predicate definitions for class invariants
/// - Pointer member validity constraints (\\valid, \\valid_read)
/// - Array member bounds constraints (\\valid(arr + (0..capacity-1)))
/// - Value relationship constraints (size <= capacity)
/// - Virtual class vtable validity (\\valid(this->vtable))
/// - Constructor postconditions (ensures inv_ClassName(this))
/// - Method pre/postconditions (requires/ensures inv_ClassName(this))
/// - Destructor preconditions (requires inv_ClassName(this))
///
/// ACSL format:
/// /*@
///   predicate inv_ClassName(struct ClassName* this) =
///     \\valid(this) &&
///     this->capacity > 0 &&
///     this->size <= this->capacity &&
///     \\valid(this->data + (0..this->capacity-1));
/// */
///
/// Reference: https://frama-c.com/html/acsl.html (v1.22+)
class ACSLClassAnnotator : public ACSLGenerator {
public:
    /// @brief Default constructor - inherits ACSL level from base
    ACSLClassAnnotator();

    /// @brief Constructor with specific ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLClassAnnotator(ACSLLevel level);

    /// @brief Constructor with ACSL level and output mode
    /// @param level ACSL coverage level (Basic or Full)
    /// @param mode Output mode (Inline or Separate)
    ACSLClassAnnotator(ACSLLevel level, ACSLOutputMode mode);

    /// @brief Generate complete ACSL class invariant predicate
    /// @param recordDecl Class declaration to analyze
    /// @return Complete ACSL predicate as formatted comment block
    ///
    /// Example output:
    /// /*@
    ///   predicate inv_Stack(struct Stack* this) =
    ///     \\valid(this) &&
    ///     this->capacity > 0 &&
    ///     this->size <= this->capacity &&
    ///     \\valid(this->data + (0..this->capacity-1));
    /// */
    std::string generateClassInvariantPredicate(const clang::CXXRecordDecl* recordDecl);

    /// @brief Generate ACSL constraints for a specific member field
    /// @param field Field declaration to analyze
    /// @return ACSL constraint string for this field
    ///
    /// Generated constraints:
    /// - Pointer members: \\valid(this->ptr) || this->ptr == \\null
    /// - Array members: \\valid(this->arr + (0..capacity-1))
    /// - Value constraints: this->size <= this->capacity
    /// - Unsigned types: this->value >= 0 (implicit, for documentation)
    std::string generateMemberConstraints(const clang::FieldDecl* field);

    /// @brief Inject class invariant in constructor postcondition
    /// @param ctor Constructor declaration
    /// @param recordDecl Class declaration (for invariant predicate name)
    /// @return ACSL ensures clause ensuring class invariant
    ///
    /// Example output:
    /// /*@ ensures inv_ClassName(this); */
    std::string injectInvariantInConstructor(const clang::CXXConstructorDecl* ctor,
                                              const clang::CXXRecordDecl* recordDecl);

    /// @brief Inject class invariant in method pre/postconditions
    /// @param method Method declaration
    /// @param recordDecl Class declaration (for invariant predicate name)
    /// @return ACSL requires and ensures clauses preserving class invariant
    ///
    /// Example output:
    /// /*@
    ///   requires inv_ClassName(this);
    ///   ensures inv_ClassName(this);
    /// */
    std::string injectInvariantInMethod(const clang::CXXMethodDecl* method,
                                         const clang::CXXRecordDecl* recordDecl);

    /// @brief Inject class invariant in destructor precondition
    /// @param dtor Destructor declaration
    /// @param recordDecl Class declaration (for invariant predicate name)
    /// @return ACSL requires clause requiring class invariant
    ///
    /// Example output:
    /// /*@ requires inv_ClassName(this); */
    std::string injectInvariantInDestructor(const clang::CXXDestructorDecl* dtor,
                                             const clang::CXXRecordDecl* recordDecl);

protected:
    /// @brief Analyze pointer field for validity constraints
    /// @param field Pointer field declaration
    /// @return Validity constraint string (e.g., "\\valid(this->ptr)")
    std::string analyzePointerField(const clang::FieldDecl* field);

    /// @brief Analyze array field for bounds constraints
    /// @param field Array field declaration
    /// @param recordDecl Parent class (to find capacity member)
    /// @return Bounds constraint string (e.g., "\\valid(this->arr + (0..capacity-1))")
    std::string analyzeArrayField(const clang::FieldDecl* field,
                                   const clang::CXXRecordDecl* recordDecl);

    /// @brief Detect value relationship constraints between members
    /// @param recordDecl Class declaration
    /// @return Vector of relationship constraints (e.g., "size <= capacity")
    std::vector<std::string> detectMemberRelationships(const clang::CXXRecordDecl* recordDecl);

    /// @brief Check if class has virtual methods (requires vtable)
    /// @param recordDecl Class declaration
    /// @return true if class has virtual methods
    bool hasVirtualMethods(const clang::CXXRecordDecl* recordDecl);

    /// @brief Generate vtable validity constraint for virtual classes
    /// @param recordDecl Class declaration
    /// @return Vtable validity constraint (e.g., "\\valid(this->vtable)")
    std::string generateVtableConstraint(const clang::CXXRecordDecl* recordDecl);

    /// @brief Find capacity/size field for array bounds inference
    /// @param recordDecl Class declaration
    /// @param arrayField Array field to find capacity for
    /// @return Capacity field declaration or nullptr if not found
    const clang::FieldDecl* findCapacityField(const clang::CXXRecordDecl* recordDecl,
                                               const clang::FieldDecl* arrayField);

    /// @brief Generate invariant predicate name from class name
    /// @param recordDecl Class declaration
    /// @return Predicate name (e.g., "inv_ClassName")
    std::string getInvariantPredicateName(const clang::CXXRecordDecl* recordDecl);

private:
    /// @brief Helper: Check if field is a pointer type
    /// @param field Field declaration
    /// @return true if field is a pointer
    bool isPointerField(const clang::FieldDecl* field);

    /// @brief Helper: Check if field is an array type
    /// @param field Field declaration
    /// @return true if field is an array (pointer or native array)
    bool isArrayField(const clang::FieldDecl* field);

    /// @brief Helper: Check if field name suggests size/count
    /// @param field Field declaration
    /// @return true if name like "size", "count", "length", "num", etc.
    bool isSizeField(const clang::FieldDecl* field);

    /// @brief Helper: Check if field name suggests capacity/max
    /// @param field Field declaration
    /// @return true if name like "capacity", "max", "limit", etc.
    bool isCapacityField(const clang::FieldDecl* field);

    /// @brief Helper: Check if pointer field is const
    /// @param field Field declaration
    /// @return true if field is const T* (pointee is const)
    bool isConstPointerField(const clang::FieldDecl* field);

    /// @brief Helper: Format predicate body with proper indentation
    /// @param constraints Vector of constraint strings
    /// @return Formatted predicate body with && operators
    std::string formatPredicateBody(const std::vector<std::string>& constraints);
};

#endif // ACSL_CLASS_ANNOTATOR_H
