/**
 * @file IteratorTypeAnalyzer.h
 * @brief Analyzer for iterator types in custom containers (Phase 54)
 *
 * Analyzes iterator types to determine:
 * - Iterator type declaration
 * - Element type (from operator* return type)
 * - Iterator operations (operator*, operator++, operator!=)
 * - Whether iterator is pointer-like or struct-based
 *
 * Scope (Phase 54 - Task 2):
 * - Extract iterator type from begin() method return type
 * - Detect iterator operations (operator overloads)
 * - Determine element type from dereference operator
 * - Support both pointer iterators (T*) and custom struct iterators
 *
 * Iterator Protocol Requirements:
 * - operator*() -> T or T&: Dereference to get element
 * - operator++(): Increment iterator (prefix)
 * - operator!=(const Iterator&): Comparison for loop termination
 *
 * Example Iterator Types:
 * - T* (pointer iterator): Uses pointer arithmetic
 * - struct Iterator { T* ptr; ... }: Custom struct with operator overloads
 */

#pragma once

#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include <optional>
#include <string>

namespace cpptoc {

/**
 * @struct IteratorOperations
 * @brief Information about iterator operations found
 */
struct IteratorOperations {
    /// operator*() - dereference to get element
    const clang::CXXMethodDecl* derefOp = nullptr;

    /// operator++() - prefix increment
    const clang::CXXMethodDecl* incrementOp = nullptr;

    /// operator!=(const Iterator&) - inequality comparison
    const clang::CXXMethodDecl* notEqualOp = nullptr;

    /// Are all required operations present?
    bool isComplete() const {
        return derefOp != nullptr && incrementOp != nullptr && notEqualOp != nullptr;
    }
};

/**
 * @struct IteratorClassification
 * @brief Complete classification of an iterator type
 */
struct IteratorClassification {
    /// Iterator type (may be pointer or struct)
    clang::QualType iteratorType;

    /// Element type (from operator* return type)
    clang::QualType elementType;

    /// Is this a pointer iterator (T*)?
    bool isPointer = false;

    /// Is this a struct-based iterator?
    bool isStruct = false;

    /// Iterator operations (for struct iterators)
    IteratorOperations operations;

    /// Iterator type name (for diagnostics)
    std::string typeName;

    /// Is this a valid, translatable iterator?
    bool isValid() const {
        if (isPointer) {
            return !elementType.isNull();
        }
        if (isStruct) {
            return operations.isComplete() && !elementType.isNull();
        }
        return false;
    }
};

/**
 * @class IteratorTypeAnalyzer
 * @brief Analyzes iterator types for custom containers
 *
 * Follows Single Responsibility Principle - only analyzes iterator types,
 * does not perform translation or code generation.
 */
class IteratorTypeAnalyzer {
public:
    /**
     * @brief Analyze an iterator type
     * @param iteratorType Iterator type from begin() return type
     * @return Iterator classification
     */
    IteratorClassification analyze(clang::QualType iteratorType);

    /**
     * @brief Extract iterator type from begin() method
     * @param beginMethod The begin() method declaration
     * @return Iterator type, or null QualType if not found
     */
    static clang::QualType getIteratorTypeFromBegin(
        const clang::CXXMethodDecl* beginMethod
    );

    /**
     * @brief Extract element type from dereference operator
     * @param iteratorType Iterator type
     * @return Element type, or null QualType if not found
     */
    static clang::QualType getElementTypeFromIterator(
        clang::QualType iteratorType
    );

private:
    /**
     * @brief Check if type is a pointer iterator (T*)
     * @param type Type to check
     * @return Element type if pointer, null QualType otherwise
     */
    std::optional<clang::QualType> tryGetPointerIterator(
        clang::QualType type
    );

    /**
     * @brief Check if type is a struct-based iterator
     * @param type Type to check
     * @return Record declaration if struct iterator, nullptr otherwise
     */
    const clang::CXXRecordDecl* tryGetStructIterator(
        clang::QualType type
    );

    /**
     * @brief Find iterator operations in struct
     * @param record Iterator struct/class declaration
     * @return Iterator operations found
     */
    IteratorOperations findIteratorOperations(
        const clang::CXXRecordDecl* record
    );

    /**
     * @brief Find operator* (dereference) in struct
     * @param record Iterator struct/class declaration
     * @return operator* method, or nullptr if not found
     */
    const clang::CXXMethodDecl* findDereferenceOperator(
        const clang::CXXRecordDecl* record
    );

    /**
     * @brief Find operator++ (prefix increment) in struct
     * @param record Iterator struct/class declaration
     * @return operator++ method, or nullptr if not found
     */
    const clang::CXXMethodDecl* findIncrementOperator(
        const clang::CXXRecordDecl* record
    );

    /**
     * @brief Find operator!= in struct
     * @param record Iterator struct/class declaration
     * @return operator!= method, or nullptr if not found
     */
    const clang::CXXMethodDecl* findNotEqualOperator(
        const clang::CXXRecordDecl* record
    );

    /**
     * @brief Extract element type from operator* return type
     * @param derefOp operator* method declaration
     * @return Element type (dereferenced if reference)
     */
    clang::QualType extractElementTypeFromDeref(
        const clang::CXXMethodDecl* derefOp
    );
};

} // namespace cpptoc
