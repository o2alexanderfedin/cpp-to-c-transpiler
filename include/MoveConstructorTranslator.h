/**
 * @file MoveConstructorTranslator.h
 * @brief Move Constructor Detection and Translation to C (Story #130)
 *
 * Responsibilities (Single Responsibility Principle):
 * - Detect C++ move constructors using Clang AST
 * - Generate equivalent C move constructor functions
 * - Handle pointer member nullification (ownership transfer)
 * - Handle non-pointer member copying
 *
 * Design Principles:
 * - SOLID: Single responsibility, open for extension
 * - DRY: Reuse existing AST traversal patterns
 * - KISS: Simple, clear API
 */

#ifndef MOVE_CONSTRUCTOR_TRANSLATOR_H
#define MOVE_CONSTRUCTOR_TRANSLATOR_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include <string>
#include <vector>

class MoveConstructorTranslator {
public:
    /**
     * Constructor
     * @param Context Clang AST context for type queries
     */
    explicit MoveConstructorTranslator(clang::ASTContext& Context);

    /**
     * Detect if a constructor is a move constructor
     *
     * Uses Clang's built-in isMoveConstructor() for accuracy
     *
     * @param Ctor Constructor declaration to check
     * @return true if this is a move constructor
     */
    bool isMoveConstructor(const clang::CXXConstructorDecl* Ctor) const;

    /**
     * Generate C move constructor function
     *
     * Generated signature:
     *   void ClassName_move_construct(struct ClassName *dest, struct ClassName *src)
     *
     * Behavior:
     * - Copy all member values from src to dest
     * - Nullify pointer members in src (ownership transfer)
     * - Reset non-pointer members in src as appropriate
     *
     * @param Ctor Move constructor declaration
     * @return Generated C function code
     */
    std::string generateMoveConstructor(const clang::CXXConstructorDecl* Ctor);

private:
    clang::ASTContext& Context;

    /**
     * Generate pointer member nullification code
     *
     * For each pointer member:
     *   dest->ptr = src->ptr;
     *   src->ptr = NULL;
     *
     * @param Record Class record declaration
     * @return Generated nullification code
     */
    std::string generatePointerNullification(const clang::CXXRecordDecl* Record);

    /**
     * Generate non-pointer member copy code
     *
     * For each non-pointer member:
     *   dest->member = src->member;
     *
     * @param Record Class record declaration
     * @return Generated copy code
     */
    std::string generateMemberCopies(const clang::CXXRecordDecl* Record);

    /**
     * Get C function name for move constructor
     *
     * Format: ClassName_move_construct
     *
     * @param Record Class record declaration
     * @return C function name
     */
    std::string getMoveConstructorName(const clang::CXXRecordDecl* Record) const;

    /**
     * Check if a type is a pointer type
     *
     * @param Type Quality type to check
     * @return true if pointer type
     */
    bool isPointerType(clang::QualType Type) const;
};

#endif // MOVE_CONSTRUCTOR_TRANSLATOR_H
