#ifndef ACSL_TYPE_INVARIANT_GENERATOR_H
#define ACSL_TYPE_INVARIANT_GENERATOR_H

// Phase 2 (v1.19.0): ACSL Type Invariant Generation
// Roadmap: .planning/ROADMAP.md
// Plan: .planning/phases/02-type-invariants/PLAN.md
//
// SOLID Principles:
// - Single Responsibility: Generates ACSL type invariants only
// - Open/Closed: Extends ACSLGenerator base class
// - Liskov Substitution: Can substitute ACSLGenerator where needed
// - Interface Segregation: Focused interface for type invariant generation
// - Dependency Inversion: Depends on Clang AST abstractions

#include "ACSLGenerator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Type.h"
#include <string>
#include <vector>
#include <unordered_set>

/// @brief Generates ACSL type invariants for C++ types
///
/// Produces type-level ACSL invariants that complement class invariants:
/// - Type invariant predicates for struct/class types
/// - Pointer member validity constraints
/// - Relational constraints (size <= capacity)
/// - Inheritance constraints (derived types strengthen base invariants)
/// - Template monomorphization support
/// - Circular dependency avoidance
/// - Integration with function contracts for automatic checking
///
/// ACSL format:
/// /*@
///   type invariant inv_TypeName(struct TypeName t) =
///     \valid(&t) &&
///     t.size <= t.capacity &&
///     (t.data == \null || \valid(t.data + (0..t.capacity-1)));
/// */
///
/// Reference: https://frama-c.com/html/acsl.html (v1.22+)
class ACSLTypeInvariantGenerator : public ACSLGenerator {
public:
    /// @brief Default constructor - inherits ACSL level from base
    ACSLTypeInvariantGenerator();

    /// @brief Constructor with specific ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLTypeInvariantGenerator(ACSLLevel level);

    /// @brief Constructor with ACSL level and output mode
    /// @param level ACSL coverage level (Basic or Full)
    /// @param mode Output mode (Inline or Separate)
    ACSLTypeInvariantGenerator(ACSLLevel level, ACSLOutputMode mode);

    /// @brief Generate ACSL type invariant for a type
    /// @param recordDecl Type declaration to analyze
    /// @return Complete ACSL type invariant as formatted comment block
    ///
    /// Example output:
    /// /*@
    ///   type invariant inv_Stack(struct Stack t) =
    ///     \valid(&t) &&
    ///     t.capacity > 0 &&
    ///     t.size <= t.capacity &&
    ///     (t.data == \null || \valid(t.data + (0..t.capacity-1)));
    /// */
    std::string generateTypeInvariant(const clang::CXXRecordDecl* recordDecl);

    /// @brief Extract type invariant from existing class invariant predicate
    /// @param classInvariantPredicate Class invariant from ACSLClassAnnotator
    /// @param recordDecl Type declaration
    /// @return Type invariant extracted and promoted from class invariant
    ///
    /// Converts class invariants (with 'this' parameter) to type invariants
    /// (with value parameter). Example:
    /// From: predicate inv_Stack(struct Stack* this) = \valid(this) && ...
    /// To:   type invariant inv_Stack(struct Stack t) = \valid(&t) && ...
    std::string extractFromClassInvariant(const std::string& classInvariantPredicate,
                                          const clang::CXXRecordDecl* recordDecl);

    /// @brief Generate type invariant for template specialization
    /// @param templateDecl Template specialization declaration
    /// @return Type invariant for monomorphized template
    std::string generateTemplateTypeInvariant(const clang::ClassTemplateSpecializationDecl* templateDecl);

protected:
    /// @brief Generate constraints for a specific field in type invariant context
    /// @param field Field declaration
    /// @param typeName Name of the containing type (for parameter reference)
    /// @return ACSL constraint string for this field
    ///
    /// Uses value semantics: t.field instead of this->field
    std::string generateFieldConstraint(const clang::FieldDecl* field,
                                        const std::string& typeName);

    /// @brief Detect and generate relational constraints between fields
    /// @param recordDecl Type declaration
    /// @param typeName Type name for parameter reference
    /// @return Vector of relational constraints (e.g., "t.size <= t.capacity")
    std::vector<std::string> detectFieldRelationships(const clang::CXXRecordDecl* recordDecl,
                                                       const std::string& typeName);

    /// @brief Generate constraints for base class invariants in derived type
    /// @param recordDecl Derived type declaration
    /// @param typeName Type name for parameter reference
    /// @return Base class invariant constraints
    ///
    /// Derived type invariants strengthen base invariants
    std::vector<std::string> generateBaseClassConstraints(const clang::CXXRecordDecl* recordDecl,
                                                           const std::string& typeName);

    /// @brief Check if type participates in circular dependency
    /// @param recordDecl Type to check
    /// @param visited Set of already visited types
    /// @return true if circular dependency detected
    bool hasCircularDependency(const clang::CXXRecordDecl* recordDecl,
                               std::unordered_set<const clang::Type*>& visited);

    /// @brief Generate pointer member constraint with value semantics
    /// @param field Pointer field
    /// @param typeName Type name for parameter reference
    /// @return Pointer validity constraint (e.g., "t.ptr == \\null || \\valid(t.ptr)")
    std::string generatePointerConstraint(const clang::FieldDecl* field,
                                         const std::string& typeName);

    /// @brief Generate array member constraint with value semantics
    /// @param field Array field
    /// @param recordDecl Containing type
    /// @param typeName Type name for parameter reference
    /// @return Array bounds constraint
    std::string generateArrayConstraint(const clang::FieldDecl* field,
                                        const clang::CXXRecordDecl* recordDecl,
                                        const std::string& typeName);

    /// @brief Generate enum member constraint
    /// @param field Enum field
    /// @param typeName Type name for parameter reference
    /// @return Enum range constraint
    std::string generateEnumConstraint(const clang::FieldDecl* field,
                                      const std::string& typeName);

    /// @brief Generate constraint for nested/composed type
    /// @param field Field with nested type
    /// @param typeName Type name for parameter reference
    /// @return Nested type constraint (may reference nested type invariant)
    std::string generateNestedTypeConstraint(const clang::FieldDecl* field,
                                            const std::string& typeName);

    /// @brief Get type invariant name from type name
    /// @param recordDecl Type declaration
    /// @return Type invariant name (e.g., "inv_TypeName")
    std::string getTypeInvariantName(const clang::CXXRecordDecl* recordDecl);

    /// @brief Format type invariant body with proper syntax
    /// @param typeName Name of the type
    /// @param constraints Vector of constraint strings
    /// @return Formatted type invariant body
    std::string formatTypeInvariantBody(const std::string& typeName,
                                       const std::vector<std::string>& constraints);

private:
    /// @brief Helper: Check if field is a pointer type
    /// @param field Field declaration
    /// @return true if field is a pointer
    bool isPointerField(const clang::FieldDecl* field);

    /// @brief Helper: Check if field is an array type
    /// @param field Field declaration
    /// @return true if field is an array
    bool isArrayField(const clang::FieldDecl* field);

    /// @brief Helper: Check if field is an enum type
    /// @param field Field declaration
    /// @return true if field is an enum
    bool isEnumField(const clang::FieldDecl* field);

    /// @brief Helper: Check if field is a nested struct/class type
    /// @param field Field declaration
    /// @return true if field is a nested type
    bool isNestedTypeField(const clang::FieldDecl* field);

    /// @brief Helper: Find capacity field for array bounds
    /// @param recordDecl Type declaration
    /// @param arrayField Array field to find capacity for
    /// @return Capacity field or nullptr
    const clang::FieldDecl* findCapacityField(const clang::CXXRecordDecl* recordDecl,
                                              const clang::FieldDecl* arrayField);

    /// @brief Helper: Check if field name suggests size/count
    /// @param field Field declaration
    /// @return true if name like "size", "count", "length", etc.
    bool isSizeField(const clang::FieldDecl* field);

    /// @brief Helper: Check if field name suggests capacity/max
    /// @param field Field declaration
    /// @return true if name like "capacity", "max", "limit", etc.
    bool isCapacityField(const clang::FieldDecl* field);

    /// @brief Helper: Check if pointer field is const
    /// @param field Field declaration
    /// @return true if field is const T* (pointee is const)
    bool isConstPointerField(const clang::FieldDecl* field);

    /// @brief Set of types currently being processed (for circular dependency detection)
    std::unordered_set<const clang::Type*> m_processingTypes;
};

#endif // ACSL_TYPE_INVARIANT_GENERATOR_H
