/**
 * @file MoveAssignmentTranslator.cpp
 * @brief Implementation of Move Assignment Operator Translation (Story #131)
 *
 * Key Implementation Points:
 * 1. Self-assignment check prevents double-free bugs
 * 2. Destructor call before transfer prevents memory leaks
 * 3. Member transfer reuses patterns from MoveConstructorTranslator
 * 4. Source nullification prevents double-free
 */

#include "../include/MoveAssignmentTranslator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include <sstream>

using namespace clang;

MoveAssignmentTranslator::MoveAssignmentTranslator(ASTContext& Context)
    : Context(Context) {}

bool MoveAssignmentTranslator::isMoveAssignmentOperator(const CXXMethodDecl* Method) const {
    if (!Method) {
        return false;
    }

    // Use Clang's built-in detection (most reliable)
    return Method->isMoveAssignmentOperator();
}

std::string MoveAssignmentTranslator::generateMoveAssignment(const CXXMethodDecl* Method) {
    if (!Method || !isMoveAssignmentOperator(Method)) {
        return "";
    }

    const CXXRecordDecl* Record = Method->getParent();
    if (!Record) {
        return "";
    }

    std::ostringstream code;
    std::string className = Record->getNameAsString();
    std::string funcName = getMoveAssignmentName(Record);

    // Generate function signature
    // Note: In C, we return void (not *this like C++)
    code << "// Move assignment operator for " << className << "\n";
    code << "void " << funcName << "(struct " << className << " *this, struct "
         << className << " *src) {\n";

    // Step 1: Self-assignment check (CRITICAL for preventing double-free)
    code << generateSelfAssignmentCheck();

    // Step 2: Call destructor on 'this' to clean up existing resources
    // This prevents memory leaks by freeing old resources before assignment
    code << generateDestructorCall(Record);

    // Step 3: Transfer members from src to this
    code << generateMemberTransfer(Record);

    // Step 4: Nullify/reset src members to prevent double-free
    code << generateSourceNullification(Record);

    code << "}\n";

    return code.str();
}

std::string MoveAssignmentTranslator::generateSelfAssignmentCheck() const {
    std::ostringstream code;

    // Generate self-assignment check
    // This is CRITICAL to prevent double-free when: a = std::move(a)
    code << "    // Self-assignment check (prevents double-free)\n";
    code << "    if (this == src) {\n";
    code << "        return;\n";
    code << "    }\n\n";

    return code.str();
}

std::string MoveAssignmentTranslator::generateDestructorCall(const CXXRecordDecl* Record) const {
    if (!Record) {
        return "";
    }

    std::ostringstream code;
    std::string className = Record->getNameAsString();

    // Generate destructor call to clean up existing resources
    // This is CRITICAL to prevent memory leaks
    code << "    // Clean up existing resources before assignment\n";
    code << "    " << className << "_destructor(this);\n\n";

    return code.str();
}

std::string MoveAssignmentTranslator::generateMemberTransfer(const CXXRecordDecl* Record) const {
    if (!Record) {
        return "";
    }

    std::ostringstream code;

    // Transfer all members from src to this
    code << "    // Transfer members from src to this\n";
    for (const auto* Field : Record->fields()) {
        std::string fieldName = Field->getNameAsString();
        code << "    this->" << fieldName << " = src->" << fieldName << ";\n";
    }
    code << "\n";

    return code.str();
}

std::string MoveAssignmentTranslator::generateSourceNullification(const CXXRecordDecl* Record) const {
    if (!Record) {
        return "";
    }

    std::ostringstream code;

    // Nullify/reset source members (ownership transfer for pointers, clean state for others)
    code << "    // Nullify/reset source members (prevent double-free)\n";
    for (const auto* Field : Record->fields()) {
        std::string fieldName = Field->getNameAsString();
        QualType fieldType = Field->getType();

        if (isPointerType(fieldType)) {
            // Nullify pointers in source (CRITICAL for preventing double-free)
            code << "    src->" << fieldName << " = NULL;\n";
        } else if (fieldType->isIntegerType()) {
            // Reset integers to 0
            code << "    src->" << fieldName << " = 0;\n";
        } else if (fieldType->isBooleanType()) {
            // Reset booleans to false
            code << "    src->" << fieldName << " = 0;\n";
        } else if (fieldType->isFloatingType()) {
            // Reset floats/doubles to 0.0
            code << "    src->" << fieldName << " = 0.0;\n";
        }
        // For other types (e.g., class types), leave them as-is
        // They will have their own move semantics handled
    }

    return code.str();
}

std::string MoveAssignmentTranslator::getMoveAssignmentName(const CXXRecordDecl* Record) const {
    if (!Record) {
        return "";
    }

    // Follow naming convention: ClassName_move_assign
    return Record->getNameAsString() + "_move_assign";
}

bool MoveAssignmentTranslator::isPointerType(QualType Type) const {
    // Remove qualifiers and get canonical type
    Type = Type.getCanonicalType();
    Type.removeLocalConst();

    return Type->isPointerType();
}
