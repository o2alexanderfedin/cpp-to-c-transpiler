/**
 * @file IteratorTypeAnalyzer.cpp
 * @brief Implementation of IteratorTypeAnalyzer
 *
 * TDD Implementation: Start with pointer iterators, expand to struct iterators.
 */

#include "handlers/IteratorTypeAnalyzer.h"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

IteratorClassification IteratorTypeAnalyzer::analyze(clang::QualType iteratorType) {
    if (iteratorType.isNull()) {
        return IteratorClassification{};
    }

    IteratorClassification result;
    result.iteratorType = iteratorType;
    result.typeName = iteratorType.getAsString();

    // Try pointer iterator first (simplest case)
    auto pointerElemType = tryGetPointerIterator(iteratorType);
    if (pointerElemType.has_value()) {
        result.isPointer = true;
        result.elementType = pointerElemType.value();
        return result;
    }

    // Try struct-based iterator
    const clang::CXXRecordDecl* record = tryGetStructIterator(iteratorType);
    if (record) {
        result.isStruct = true;
        result.operations = findIteratorOperations(record);

        // Extract element type from operator*
        if (result.operations.derefOp) {
            result.elementType = extractElementTypeFromDeref(result.operations.derefOp);
        }

        return result;
    }

    // Unknown/unsupported iterator type
    return IteratorClassification{};
}

clang::QualType IteratorTypeAnalyzer::getIteratorTypeFromBegin(
    const clang::CXXMethodDecl* beginMethod
) {
    if (!beginMethod) {
        return clang::QualType();
    }

    // Return type is the iterator type
    return beginMethod->getReturnType();
}

clang::QualType IteratorTypeAnalyzer::getElementTypeFromIterator(
    clang::QualType iteratorType
) {
    IteratorTypeAnalyzer analyzer;
    IteratorClassification classification = analyzer.analyze(iteratorType);
    return classification.elementType;
}

std::optional<clang::QualType> IteratorTypeAnalyzer::tryGetPointerIterator(
    clang::QualType type
) {
    // Remove qualifiers
    type = type.getUnqualifiedType();

    // Check if it's a pointer type
    if (const auto* PT = type->getAs<clang::PointerType>()) {
        // Element type is what the pointer points to
        return PT->getPointeeType();
    }

    return std::nullopt;
}

const clang::CXXRecordDecl* IteratorTypeAnalyzer::tryGetStructIterator(
    clang::QualType type
) {
    // Remove qualifiers
    type = type.getUnqualifiedType();

    // Check if it's a class/struct type
    if (const auto* RT = type->getAs<clang::RecordType>()) {
        // Must be a CXX record (class/struct) to have operator overloads
        return llvm::dyn_cast_or_null<clang::CXXRecordDecl>(RT->getDecl());
    }

    return nullptr;
}

IteratorOperations IteratorTypeAnalyzer::findIteratorOperations(
    const clang::CXXRecordDecl* record
) {
    if (!record) {
        return IteratorOperations{};
    }

    IteratorOperations ops;
    ops.derefOp = findDereferenceOperator(record);
    ops.incrementOp = findIncrementOperator(record);
    ops.notEqualOp = findNotEqualOperator(record);

    return ops;
}

const clang::CXXMethodDecl* IteratorTypeAnalyzer::findDereferenceOperator(
    const clang::CXXRecordDecl* record
) {
    if (!record) return nullptr;

    // Look for operator*
    for (const auto* method : record->methods()) {
        if (method->getOverloadedOperator() == clang::OO_Star) {
            // Found operator*
            return method;
        }
    }

    return nullptr;
}

const clang::CXXMethodDecl* IteratorTypeAnalyzer::findIncrementOperator(
    const clang::CXXRecordDecl* record
) {
    if (!record) return nullptr;

    // Look for operator++ (prefix)
    // Prefix has 0 parameters (besides implicit this)
    for (const auto* method : record->methods()) {
        if (method->getOverloadedOperator() == clang::OO_PlusPlus) {
            // Check if it's prefix (no parameters)
            if (method->getNumParams() == 0) {
                return method;
            }
        }
    }

    return nullptr;
}

const clang::CXXMethodDecl* IteratorTypeAnalyzer::findNotEqualOperator(
    const clang::CXXRecordDecl* record
) {
    if (!record) return nullptr;

    // Look for operator!=
    for (const auto* method : record->methods()) {
        if (method->getOverloadedOperator() == clang::OO_ExclaimEqual) {
            return method;
        }
    }

    return nullptr;
}

clang::QualType IteratorTypeAnalyzer::extractElementTypeFromDeref(
    const clang::CXXMethodDecl* derefOp
) {
    if (!derefOp) {
        return clang::QualType();
    }

    clang::QualType returnType = derefOp->getReturnType();

    // If return type is a reference, get the underlying type
    if (const auto* RT = returnType->getAs<clang::ReferenceType>()) {
        return RT->getPointeeType();
    }

    // Otherwise, return as-is
    return returnType;
}

} // namespace cpptoc
