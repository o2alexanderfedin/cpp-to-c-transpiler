/**
 * @file MoveConstructorTranslator.cpp
 * @brief Implementation of Move Constructor Translation (Story #130)
 */

#include "../include/MoveConstructorTranslator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include <sstream>

using namespace clang;

MoveConstructorTranslator::MoveConstructorTranslator(ASTContext& Context)
    : Context(Context) {}

bool MoveConstructorTranslator::isMoveConstructor(const CXXConstructorDecl* Ctor) const {
    if (!Ctor) {
        return false;
    }

    // Use Clang's built-in detection (most reliable)
    return Ctor->isMoveConstructor();
}

std::string MoveConstructorTranslator::generateMoveConstructor(const CXXConstructorDecl* Ctor) {
    if (!Ctor || !isMoveConstructor(Ctor)) {
        return "";
    }

    const CXXRecordDecl* Record = Ctor->getParent();
    if (!Record) {
        return "";
    }

    std::ostringstream code;
    std::string className = Record->getNameAsString();
    std::string funcName = getMoveConstructorName(Record);

    // Generate function signature
    code << "// Move constructor for " << className << "\n";
    code << "void " << funcName << "(struct " << className << " *dest, struct "
         << className << " *src) {\n";

    // Generate member-by-member move logic
    // Strategy:
    // 1. Copy all members from src to dest
    // 2. For pointer members: nullify src after copy
    // 3. For non-pointer members: reset to zero/false

    for (const auto* Field : Record->fields()) {
        std::string fieldName = Field->getNameAsString();
        QualType fieldType = Field->getType();

        // Copy member from src to dest
        code << "    dest->" << fieldName << " = src->" << fieldName << ";\n";
    }

    // Reset source members (ownership transfer for pointers, clean state for others)
    for (const auto* Field : Record->fields()) {
        std::string fieldName = Field->getNameAsString();
        QualType fieldType = Field->getType();

        if (isPointerType(fieldType)) {
            // Nullify pointers in source
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

    // Translate constructor body if present
    // The body typically contains additional nullification or reset logic
    if (Ctor->hasBody()) {
        const Stmt* Body = Ctor->getBody();
        if (const CompoundStmt* CS = dyn_cast<CompoundStmt>(Body)) {
            // Add comment for body translation
            code << "    // Constructor body (simplified translation)\n";

            // For now, we rely on the automatic member copy above
            // In a full implementation, we'd translate each statement
            // This is a simplified version for the POC
        }
    }

    code << "}\n";

    return code.str();
}

std::string MoveConstructorTranslator::generatePointerNullification(const CXXRecordDecl* Record) {
    if (!Record) {
        return "";
    }

    std::ostringstream code;

    for (const auto* Field : Record->fields()) {
        if (isPointerType(Field->getType())) {
            std::string fieldName = Field->getNameAsString();
            code << "    src->" << fieldName << " = NULL;\n";
        }
    }

    return code.str();
}

std::string MoveConstructorTranslator::generateMemberCopies(const CXXRecordDecl* Record) {
    if (!Record) {
        return "";
    }

    std::ostringstream code;

    for (const auto* Field : Record->fields()) {
        std::string fieldName = Field->getNameAsString();
        code << "    dest->" << fieldName << " = src->" << fieldName << ";\n";
    }

    return code.str();
}

std::string MoveConstructorTranslator::getMoveConstructorName(const CXXRecordDecl* Record) const {
    if (!Record) {
        return "";
    }

    return Record->getNameAsString() + "_move_construct";
}

bool MoveConstructorTranslator::isPointerType(QualType Type) const {
    // Remove qualifiers and get canonical type
    Type = Type.getCanonicalType();
    Type.removeLocalConst();

    return Type->isPointerType();
}
