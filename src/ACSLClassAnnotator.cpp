// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #198: ACSLClassAnnotator for class invariant predicates
//
// Implementation following SOLID and TDD principles

#include "ACSLClassAnnotator.h"
#include <algorithm>
#include <sstream>

using namespace clang;

// Constructors
ACSLClassAnnotator::ACSLClassAnnotator()
    : ACSLGenerator() {
}

ACSLClassAnnotator::ACSLClassAnnotator(ACSLLevel level)
    : ACSLGenerator(level) {
}

ACSLClassAnnotator::ACSLClassAnnotator(ACSLLevel level, ACSLOutputMode mode)
    : ACSLGenerator(level, mode) {
}

// Main predicate generation method
std::string ACSLClassAnnotator::generateClassInvariantPredicate(const CXXRecordDecl* recordDecl) {
    if (!recordDecl) return "";

    std::vector<std::string> constraints;

    // Always validate this pointer
    constraints.push_back("\\valid(this)");

    // Analyze each field for constraints
    for (const auto* field : recordDecl->fields()) {
        std::string fieldConstraint = generateMemberConstraints(field);
        if (!fieldConstraint.empty()) {
            constraints.push_back(fieldConstraint);
        }
    }

    // Detect value relationships (size <= capacity, etc.)
    std::vector<std::string> relationships = detectMemberRelationships(recordDecl);
    constraints.insert(constraints.end(), relationships.begin(), relationships.end());

    // Virtual class vtable constraint
    if (hasVirtualMethods(recordDecl)) {
        std::string vtableConstraint = generateVtableConstraint(recordDecl);
        if (!vtableConstraint.empty()) {
            constraints.push_back(vtableConstraint);
        }
    }

    // Build predicate
    std::ostringstream oss;
    std::string predicateName = getInvariantPredicateName(recordDecl);
    std::string className = recordDecl->getNameAsString();

    oss << "predicate " << predicateName << "(struct " << className << "* this) =\n";
    oss << formatPredicateBody(constraints);

    return formatACSLComment(oss.str());
}

// Generate member constraints
std::string ACSLClassAnnotator::generateMemberConstraints(const FieldDecl* field) {
    if (!field) return "";

    // Pointer fields
    if (isPointerField(field)) {
        return analyzePointerField(field);
    }

    // Array fields (handled separately with capacity detection)
    // This is covered in analyzePointerField and detectMemberRelationships

    // Value constraints for unsigned types (documentation)
    QualType type = field->getType();
    if (type->isUnsignedIntegerType()) {
        std::string fieldName = field->getNameAsString();
        return "this->" + fieldName + " >= 0";
    }

    return "";
}

// Inject invariant in constructor
std::string ACSLClassAnnotator::injectInvariantInConstructor(const CXXConstructorDecl* ctor,
                                                              const CXXRecordDecl* recordDecl) {
    if (!ctor || !recordDecl) return "";

    std::string predicateName = getInvariantPredicateName(recordDecl);
    std::ostringstream oss;
    oss << "ensures " << predicateName << "(this);";

    return formatACSLComment(oss.str());
}

// Inject invariant in method
std::string ACSLClassAnnotator::injectInvariantInMethod(const CXXMethodDecl* method,
                                                         const CXXRecordDecl* recordDecl) {
    if (!method || !recordDecl) return "";

    std::string predicateName = getInvariantPredicateName(recordDecl);
    std::ostringstream oss;
    oss << "requires " << predicateName << "(this);\n";
    oss << "  ensures " << predicateName << "(this);";

    return formatACSLComment(oss.str());
}

// Inject invariant in destructor
std::string ACSLClassAnnotator::injectInvariantInDestructor(const CXXDestructorDecl* dtor,
                                                             const CXXRecordDecl* recordDecl) {
    if (!dtor || !recordDecl) return "";

    std::string predicateName = getInvariantPredicateName(recordDecl);
    std::ostringstream oss;
    oss << "requires " << predicateName << "(this);";

    return formatACSLComment(oss.str());
}

// Analyze pointer field
std::string ACSLClassAnnotator::analyzePointerField(const FieldDecl* field) {
    if (!field) return "";

    std::string fieldName = field->getNameAsString();
    std::ostringstream oss;

    // Check if const pointer
    if (isConstPointerField(field)) {
        oss << "\\valid_read(this->" << fieldName << ") || this->" << fieldName << " == \\null";
    } else {
        oss << "\\valid(this->" << fieldName << ") || this->" << fieldName << " == \\null";
    }

    return oss.str();
}

// Analyze array field
std::string ACSLClassAnnotator::analyzeArrayField(const FieldDecl* field,
                                                   const CXXRecordDecl* recordDecl) {
    if (!field || !recordDecl) return "";

    std::string fieldName = field->getNameAsString();
    const FieldDecl* capacityField = findCapacityField(recordDecl, field);

    std::ostringstream oss;

    if (capacityField) {
        std::string capacityName = capacityField->getNameAsString();
        if (isConstPointerField(field)) {
            oss << "\\valid_read(this->" << fieldName << " + (0..this->" << capacityName << "-1))";
        } else {
            oss << "\\valid(this->" << fieldName << " + (0..this->" << capacityName << "-1))";
        }
    } else {
        // No capacity field found, use simple validity
        if (isConstPointerField(field)) {
            oss << "\\valid_read(this->" << fieldName << ")";
        } else {
            oss << "\\valid(this->" << fieldName << ")";
        }
    }

    return oss.str();
}

// Detect member relationships
std::vector<std::string> ACSLClassAnnotator::detectMemberRelationships(const CXXRecordDecl* recordDecl) {
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
        oss << "this->" << capacityField->getNameAsString() << " > 0";
        relationships.push_back(oss.str());
    }

    // Size <= Capacity relationship
    if (sizeField && capacityField) {
        std::ostringstream oss;
        oss << "this->" << sizeField->getNameAsString() << " <= this->"
            << capacityField->getNameAsString();
        relationships.push_back(oss.str());
    }

    // Array bounds with capacity
    if (arrayField && capacityField) {
        std::string arrayConstraint = analyzeArrayField(arrayField, recordDecl);
        if (!arrayConstraint.empty()) {
            relationships.push_back(arrayConstraint);
        }
    }

    return relationships;
}

// Check if class has virtual methods
bool ACSLClassAnnotator::hasVirtualMethods(const CXXRecordDecl* recordDecl) {
    if (!recordDecl) return false;

    // Check for virtual methods
    for (const auto* method : recordDecl->methods()) {
        if (method->isVirtual()) {
            return true;
        }
    }

    return false;
}

// Generate vtable constraint
std::string ACSLClassAnnotator::generateVtableConstraint(const CXXRecordDecl* recordDecl) {
    if (!recordDecl) return "";

    // Only generate if class actually has virtual methods
    if (!hasVirtualMethods(recordDecl)) {
        return "";
    }

    return "\\valid(this->vtable)";
}

// Find capacity field for array
const FieldDecl* ACSLClassAnnotator::findCapacityField(const CXXRecordDecl* recordDecl,
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

// Get invariant predicate name
std::string ACSLClassAnnotator::getInvariantPredicateName(const CXXRecordDecl* recordDecl) {
    if (!recordDecl) return "";

    std::string className = recordDecl->getNameAsString();
    return "inv_" + className;
}

// Helper: Check if field is pointer
bool ACSLClassAnnotator::isPointerField(const FieldDecl* field) {
    if (!field) return false;
    return field->getType()->isPointerType();
}

// Helper: Check if field is array
bool ACSLClassAnnotator::isArrayField(const FieldDecl* field) {
    if (!field) return false;

    QualType type = field->getType();
    return type->isPointerType() || type->isArrayType();
}

// Helper: Check if field is size field
bool ACSLClassAnnotator::isSizeField(const FieldDecl* field) {
    if (!field) return false;

    std::string name = field->getNameAsString();
    std::transform(name.begin(), name.end(), name.begin(), ::tolower);

    return name == "size" || name == "count" || name == "length" ||
           name == "num" || name == "len" ||
           name.find("size") != std::string::npos ||
           name.find("count") != std::string::npos;
}

// Helper: Check if field is capacity field
bool ACSLClassAnnotator::isCapacityField(const FieldDecl* field) {
    if (!field) return false;

    std::string name = field->getNameAsString();
    std::transform(name.begin(), name.end(), name.begin(), ::tolower);

    return name == "capacity" || name == "cap" || name == "max" ||
           name == "limit" || name == "maximum" ||
           name.find("capacity") != std::string::npos ||
           name.find("max") != std::string::npos;
}

// Helper: Check if pointer field is const
bool ACSLClassAnnotator::isConstPointerField(const FieldDecl* field) {
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

// Helper: Format predicate body
std::string ACSLClassAnnotator::formatPredicateBody(const std::vector<std::string>& constraints) {
    if (constraints.empty()) {
        return "    \\true;";
    }

    std::ostringstream oss;
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
