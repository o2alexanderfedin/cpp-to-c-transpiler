// Phase 2 (v1.19.0): ACSL Type Invariant Generation
// Plan: .planning/phases/02-type-invariants/PLAN.md
//
// Implementation following SOLID and TDD principles

#include "ACSLTypeInvariantGenerator.h"
#include "clang/AST/DeclTemplate.h"
#include <algorithm>
#include <sstream>

using namespace clang;

// ============================================================================
// Constructors
// ============================================================================

ACSLTypeInvariantGenerator::ACSLTypeInvariantGenerator()
    : ACSLGenerator() {
}

ACSLTypeInvariantGenerator::ACSLTypeInvariantGenerator(ACSLLevel level)
    : ACSLGenerator(level) {
}

ACSLTypeInvariantGenerator::ACSLTypeInvariantGenerator(ACSLLevel level, ACSLOutputMode mode)
    : ACSLGenerator(level, mode) {
}

// ============================================================================
// Main type invariant generation
// ============================================================================

std::string ACSLTypeInvariantGenerator::generateTypeInvariant(const CXXRecordDecl* recordDecl) {
    if (!recordDecl) return "";

    // Check for circular dependencies
    std::unordered_set<const Type*> visited;
    if (hasCircularDependency(recordDecl, visited)) {
        // For circular types, generate simplified invariant
        // to avoid infinite recursion
    }

    std::string typeName = recordDecl->getNameAsString();
    std::vector<std::string> constraints;

    // Always validate the type instance reference
    constraints.push_back("\\valid(&t)");

    // Analyze each field for constraints
    for (const auto* field : recordDecl->fields()) {
        std::string fieldConstraint = generateFieldConstraint(field, typeName);
        if (!fieldConstraint.empty()) {
            constraints.push_back(fieldConstraint);
        }
    }

    // Detect field relationships (size <= capacity, etc.)
    std::vector<std::string> relationships = detectFieldRelationships(recordDecl, typeName);
    constraints.insert(constraints.end(), relationships.begin(), relationships.end());

    // Add base class constraints for derived types
    std::vector<std::string> baseConstraints = generateBaseClassConstraints(recordDecl, typeName);
    constraints.insert(constraints.end(), baseConstraints.begin(), baseConstraints.end());

    // Build type invariant
    std::string body = formatTypeInvariantBody(typeName, constraints);

    return formatACSLComment(body);
}

std::string ACSLTypeInvariantGenerator::extractFromClassInvariant(
    const std::string& classInvariantPredicate,
    const CXXRecordDecl* recordDecl) {

    if (!recordDecl || classInvariantPredicate.empty()) return "";

    std::string typeName = recordDecl->getNameAsString();
    std::string result = classInvariantPredicate;

    // Convert from class invariant (pointer parameter) to type invariant (value parameter)
    // Replace "predicate inv_" with "type invariant inv_"
    size_t pos = result.find("predicate inv_");
    if (pos != std::string::npos) {
        result.replace(pos, 14, "type invariant inv_");
    }

    // Replace "struct TypeName* this" with "struct TypeName t"
    std::string oldParam = "struct " + typeName + "* this";
    std::string newParam = "struct " + typeName + " t";
    pos = result.find(oldParam);
    if (pos != std::string::npos) {
        result.replace(pos, oldParam.length(), newParam);
    }

    // Replace all "this->" references with "t."
    size_t start = 0;
    while ((pos = result.find("this->", start)) != std::string::npos) {
        result.replace(pos, 6, "t.");
        start = pos + 2;
    }

    // Replace "\valid(this)" with "\valid(&t)"
    start = 0;
    while ((pos = result.find("\\valid(this)", start)) != std::string::npos) {
        result.replace(pos, 12, "\\valid(&t)");
        start = pos + 10;
    }

    return result;
}

std::string ACSLTypeInvariantGenerator::generateTemplateTypeInvariant(
    const ClassTemplateSpecializationDecl* templateDecl) {

    if (!templateDecl) return "";

    // Treat template specialization as a regular type
    return generateTypeInvariant(templateDecl);
}

// ============================================================================
// Field constraint generation
// ============================================================================

std::string ACSLTypeInvariantGenerator::generateFieldConstraint(
    const FieldDecl* field,
    const std::string& typeName) {

    if (!field) return "";

    // Pointer fields
    if (isPointerField(field)) {
        return generatePointerConstraint(field, typeName);
    }

    // Array fields
    if (isArrayField(field)) {
        // Array constraints handled in detectFieldRelationships
        // to properly correlate with capacity fields
        return "";
    }

    // Enum fields
    if (isEnumField(field)) {
        return generateEnumConstraint(field, typeName);
    }

    // Nested type fields
    if (isNestedTypeField(field)) {
        return generateNestedTypeConstraint(field, typeName);
    }

    // Unsigned types (implicit constraint, documented)
    QualType type = field->getType();
    if (type->isUnsignedIntegerType()) {
        std::string fieldName = field->getNameAsString();
        return "t." + fieldName + " >= 0";
    }

    return "";
}

std::vector<std::string> ACSLTypeInvariantGenerator::detectFieldRelationships(
    const CXXRecordDecl* recordDecl,
    const std::string& typeName) {

    std::vector<std::string> relationships;
    if (!recordDecl) return relationships;

    const FieldDecl* sizeField = nullptr;
    const FieldDecl* capacityField = nullptr;
    const FieldDecl* arrayField = nullptr;

    // Find size, capacity, and array fields
    for (const auto* field : recordDecl->fields()) {
        if (isSizeField(field)) {
            sizeField = field;
        } else if (isCapacityField(field)) {
            capacityField = field;
        } else if (isPointerField(field) && !arrayField) {
            arrayField = field;
        }
    }

    // Capacity constraint (must be positive for valid arrays)
    if (capacityField && arrayField) {
        std::ostringstream oss;
        oss << "t." << capacityField->getNameAsString() << " > 0";
        relationships.push_back(oss.str());
    }

    // Size <= Capacity relationship
    if (sizeField && capacityField) {
        std::ostringstream oss;
        oss << "t." << sizeField->getNameAsString() << " <= t."
            << capacityField->getNameAsString();
        relationships.push_back(oss.str());
    }

    // Array bounds with capacity
    if (arrayField && capacityField) {
        std::string arrayConstraint = generateArrayConstraint(arrayField, recordDecl, typeName);
        if (!arrayConstraint.empty()) {
            relationships.push_back(arrayConstraint);
        }
    }

    return relationships;
}

std::vector<std::string> ACSLTypeInvariantGenerator::generateBaseClassConstraints(
    const CXXRecordDecl* recordDecl,
    const std::string& typeName) {

    std::vector<std::string> constraints;
    if (!recordDecl) return constraints;

    // For each base class, reference its type invariant
    for (const auto& base : recordDecl->bases()) {
        QualType baseType = base.getType();
        if (const RecordType* baseRecordType = baseType->getAs<RecordType>()) {
            if (const CXXRecordDecl* baseDecl = dyn_cast<CXXRecordDecl>(baseRecordType->getDecl())) {
                std::string baseName = baseDecl->getNameAsString();
                std::ostringstream oss;
                // Reference base class invariant - derived strengthens base
                oss << "inv_" << baseName << "(t." << baseName << ")";
                constraints.push_back(oss.str());
            }
        }
    }

    return constraints;
}

// ============================================================================
// Specific constraint generators
// ============================================================================

std::string ACSLTypeInvariantGenerator::generatePointerConstraint(
    const FieldDecl* field,
    const std::string& typeName) {

    if (!field) return "";

    std::string fieldName = field->getNameAsString();
    std::ostringstream oss;

    // Check if const pointer
    if (isConstPointerField(field)) {
        oss << "(t." << fieldName << " == \\null || \\valid_read(t." << fieldName << "))";
    } else {
        oss << "(t." << fieldName << " == \\null || \\valid(t." << fieldName << "))";
    }

    return oss.str();
}

std::string ACSLTypeInvariantGenerator::generateArrayConstraint(
    const FieldDecl* field,
    const CXXRecordDecl* recordDecl,
    const std::string& typeName) {

    if (!field || !recordDecl) return "";

    std::string fieldName = field->getNameAsString();
    const FieldDecl* capacityField = findCapacityField(recordDecl, field);

    std::ostringstream oss;

    if (capacityField) {
        std::string capacityName = capacityField->getNameAsString();
        if (isConstPointerField(field)) {
            oss << "(t." << fieldName << " == \\null || \\valid_read(t." << fieldName
                << " + (0..t." << capacityName << "-1)))";
        } else {
            oss << "(t." << fieldName << " == \\null || \\valid(t." << fieldName
                << " + (0..t." << capacityName << "-1)))";
        }
    } else {
        // No capacity field found, use simple validity
        if (isConstPointerField(field)) {
            oss << "(t." << fieldName << " == \\null || \\valid_read(t." << fieldName << "))";
        } else {
            oss << "(t." << fieldName << " == \\null || \\valid(t." << fieldName << "))";
        }
    }

    return oss.str();
}

std::string ACSLTypeInvariantGenerator::generateEnumConstraint(
    const FieldDecl* field,
    const std::string& typeName) {

    if (!field) return "";

    std::string fieldName = field->getNameAsString();
    QualType fieldType = field->getType();

    // Get enum declaration
    const EnumType* enumType = fieldType->getAs<EnumType>();
    if (!enumType) return "";

    const EnumDecl* enumDecl = enumType->getDecl();
    if (!enumDecl) return "";

    // For scoped enums, just validate that it's within the defined range
    // ACSL doesn't have direct enum validation, but we can check bounds
    std::ostringstream oss;

    // Get min and max enum values
    if (enumDecl->enumerator_begin() != enumDecl->enumerator_end()) {
        auto firstEnum = *enumDecl->enumerator_begin();

        // Find last enumerator manually
        const EnumConstantDecl* lastEnum = firstEnum;
        for (auto it = enumDecl->enumerator_begin(); it != enumDecl->enumerator_end(); ++it) {
            lastEnum = *it;
        }

        oss << "t." << fieldName << " >= " << firstEnum->getInitVal().getSExtValue()
            << " && t." << fieldName << " <= " << lastEnum->getInitVal().getSExtValue();
    }

    return oss.str();
}

std::string ACSLTypeInvariantGenerator::generateNestedTypeConstraint(
    const FieldDecl* field,
    const std::string& typeName) {

    if (!field) return "";

    std::string fieldName = field->getNameAsString();
    QualType fieldType = field->getType();

    // Get nested type declaration
    if (const RecordType* nestedRecordType = fieldType->getAs<RecordType>()) {
        if (const CXXRecordDecl* nestedDecl = dyn_cast<CXXRecordDecl>(nestedRecordType->getDecl())) {
            std::string nestedTypeName = nestedDecl->getNameAsString();
            std::ostringstream oss;
            // Reference nested type's invariant
            oss << "inv_" << nestedTypeName << "(t." << fieldName << ")";
            return oss.str();
        }
    }

    return "";
}

// ============================================================================
// Circular dependency detection
// ============================================================================

bool ACSLTypeInvariantGenerator::hasCircularDependency(
    const CXXRecordDecl* recordDecl,
    std::unordered_set<const Type*>& visited) {

    if (!recordDecl) return false;

    const Type* type = recordDecl->getTypeForDecl();
    if (!type) return false;

    // Check if we've already visited this type
    if (visited.find(type) != visited.end()) {
        return true; // Circular dependency detected
    }

    visited.insert(type);

    // Check all fields for circular references
    for (const auto* field : recordDecl->fields()) {
        QualType fieldType = field->getType();

        // For pointer types, check pointee type
        if (fieldType->isPointerType()) {
            QualType pointeeType = fieldType->getPointeeType();
            if (const RecordType* recordType = pointeeType->getAs<RecordType>()) {
                if (const CXXRecordDecl* fieldDecl = dyn_cast<CXXRecordDecl>(recordType->getDecl())) {
                    if (hasCircularDependency(fieldDecl, visited)) {
                        visited.erase(type); // Remove before returning
                        return true;
                    }
                }
            }
        }
        // For value types, check for direct recursion
        else if (const RecordType* recordType = fieldType->getAs<RecordType>()) {
            if (const CXXRecordDecl* fieldDecl = dyn_cast<CXXRecordDecl>(recordType->getDecl())) {
                if (hasCircularDependency(fieldDecl, visited)) {
                    visited.erase(type); // Remove before returning
                    return true;
                }
            }
        }
    }

    visited.erase(type);
    return false;
}

// ============================================================================
// Formatting and naming
// ============================================================================

std::string ACSLTypeInvariantGenerator::getTypeInvariantName(const CXXRecordDecl* recordDecl) {
    if (!recordDecl) return "";

    std::string typeName = recordDecl->getNameAsString();
    return "inv_" + typeName;
}

std::string ACSLTypeInvariantGenerator::formatTypeInvariantBody(
    const std::string& typeName,
    const std::vector<std::string>& constraints) {

    if (constraints.empty()) {
        std::ostringstream oss;
        oss << "type invariant inv_" << typeName << "(struct " << typeName << " t) =\n";
        oss << "    \\true;";
        return oss.str();
    }

    std::ostringstream oss;
    oss << "type invariant inv_" << typeName << "(struct " << typeName << " t) =\n";

    for (size_t i = 0; i < constraints.size(); ++i) {
        oss << "    " << constraints[i];
        if (i < constraints.size() - 1) {
            oss << " &&\n";
        } else {
            oss << ";";
        }
    }

    return oss.str();
}

// ============================================================================
// Helper methods
// ============================================================================

bool ACSLTypeInvariantGenerator::isPointerField(const FieldDecl* field) {
    if (!field) return false;
    return field->getType()->isPointerType();
}

bool ACSLTypeInvariantGenerator::isArrayField(const FieldDecl* field) {
    if (!field) return false;

    QualType type = field->getType();
    return type->isPointerType() || type->isArrayType();
}

bool ACSLTypeInvariantGenerator::isEnumField(const FieldDecl* field) {
    if (!field) return false;

    QualType type = field->getType();
    return type->isEnumeralType();
}

bool ACSLTypeInvariantGenerator::isNestedTypeField(const FieldDecl* field) {
    if (!field) return false;

    QualType type = field->getType();
    // Check if it's a record type (struct/class) and not a pointer
    if (type->isRecordType() && !type->isPointerType()) {
        return true;
    }

    return false;
}

const FieldDecl* ACSLTypeInvariantGenerator::findCapacityField(
    const CXXRecordDecl* recordDecl,
    const FieldDecl* arrayField) {

    if (!recordDecl || !arrayField) return nullptr;

    // Look for capacity/size fields
    for (const auto* field : recordDecl->fields()) {
        if (field == arrayField) continue;

        if (isCapacityField(field)) {
            return field;
        }
    }

    // Also check for size fields as fallback
    for (const auto* field : recordDecl->fields()) {
        if (field == arrayField) continue;

        if (isSizeField(field)) {
            return field;
        }
    }

    return nullptr;
}

bool ACSLTypeInvariantGenerator::isSizeField(const FieldDecl* field) {
    if (!field) return false;

    std::string name = field->getNameAsString();
    std::transform(name.begin(), name.end(), name.begin(), ::tolower);

    return name == "size" || name == "count" || name == "length" ||
           name == "num" || name == "len" ||
           name.find("size") != std::string::npos ||
           name.find("count") != std::string::npos;
}

bool ACSLTypeInvariantGenerator::isCapacityField(const FieldDecl* field) {
    if (!field) return false;

    std::string name = field->getNameAsString();
    std::transform(name.begin(), name.end(), name.begin(), ::tolower);

    return name == "capacity" || name == "cap" || name == "max" ||
           name == "limit" || name == "maximum" ||
           name.find("capacity") != std::string::npos ||
           name.find("max") != std::string::npos;
}

bool ACSLTypeInvariantGenerator::isConstPointerField(const FieldDecl* field) {
    if (!field) return false;

    QualType type = field->getType();

    // const T* (pointee is const)
    if (type->isPointerType()) {
        QualType pointeeType = type->getPointeeType();
        if (pointeeType.isConstQualified()) {
            return true;
        }
    }

    return false;
}
