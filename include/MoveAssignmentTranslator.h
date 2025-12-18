/**
 * @file MoveAssignmentTranslator.h
 * @brief Move Assignment Operator Detection and Translation to C (Story #131)
 *
 * Responsibilities (Single Responsibility Principle):
 * - Detect C++ move assignment operators using Clang AST
 * - Generate equivalent C move assignment functions
 * - Handle self-assignment check (prevent double-free)
 * - Call destructor before transfer (prevent memory leak)
 * - Handle pointer member nullification (ownership transfer)
 * - Handle non-pointer member reset
 *
 * Design Principles:
 * - SOLID: Single responsibility, open for extension
 * - DRY: Reuse logic from MoveConstructorTranslator
 * - KISS: Simple, clear API
 *
 * Key Differences from Move Constructor:
 * - Move assignment must check for self-assignment
 * - Move assignment must call destructor on destination before transfer
 * - Move assignment returns void in C (operator= returns *this in C++)
 */

#ifndef MOVE_ASSIGNMENT_TRANSLATOR_H
#define MOVE_ASSIGNMENT_TRANSLATOR_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include <string>

class MoveAssignmentTranslator {
public:
    /**
     * Constructor
     * @param Context Clang AST context for type queries
     */
    explicit MoveAssignmentTranslator(clang::ASTContext& Context);

    /**
     * Detect if a method is a move assignment operator
     *
     * Uses Clang's built-in isMoveAssignmentOperator() for accuracy
     *
     * @param Method Method declaration to check
     * @return true if this is a move assignment operator
     */
    bool isMoveAssignmentOperator(const clang::CXXMethodDecl* Method) const;

    /**
     * Generate C move assignment function
     *
     * Generated signature:
     *   void ClassName_move_assign(struct ClassName *this, struct ClassName *src)
     *
     * Generated structure:
     *   1. Self-assignment check: if (this == src) return;
     *   2. Destructor call: ClassName_destructor(this);
     *   3. Member transfer: this->member = src->member;
     *   4. Source nullification: src->member = NULL;
     *
     * Critical for memory safety:
     * - Self-assignment check prevents double-free
     * - Destructor call prevents memory leak
     * - Source nullification prevents double-free
     *
     * @param Method Move assignment operator declaration
     * @return Generated C function code
     */
    std::string generateMoveAssignment(const clang::CXXMethodDecl* Method);

private:
    clang::ASTContext& Context;

    /**
     * Generate self-assignment check
     *
     * Generates:
     *   if (this == src) {
     *       return;
     *   }
     *
     * Critical: Prevents double-free when a = std::move(a)
     *
     * @return Generated self-assignment check code
     */
    std::string generateSelfAssignmentCheck() const;

    /**
     * Generate destructor call for cleanup
     *
     * Generates:
     *   ClassName_destructor(this);
     *
     * Critical: Frees existing resources before assignment
     * Prevents memory leak
     *
     * @param Record Class record declaration
     * @return Generated destructor call code
     */
    std::string generateDestructorCall(const clang::CXXRecordDecl* Record) const;

    /**
     * Generate member transfer code (reuse from MoveConstructorTranslator)
     *
     * For each member:
     *   this->member = src->member;
     *
     * @param Record Class record declaration
     * @return Generated member transfer code
     */
    std::string generateMemberTransfer(const clang::CXXRecordDecl* Record) const;

    /**
     * Generate source nullification code (reuse from MoveConstructorTranslator)
     *
     * For pointer members:
     *   src->ptr = NULL;
     *
     * For non-pointer members:
     *   src->member = 0; (or appropriate reset value)
     *
     * Critical: Prevents double-free
     *
     * @param Record Class record declaration
     * @return Generated source nullification code
     */
    std::string generateSourceNullification(const clang::CXXRecordDecl* Record) const;

    /**
     * Get C function name for move assignment operator
     *
     * Format: ClassName_move_assign
     *
     * @param Record Class record declaration
     * @return C function name
     */
    std::string getMoveAssignmentName(const clang::CXXRecordDecl* Record) const;

    /**
     * Check if a type is a pointer type
     *
     * @param Type Quality type to check
     * @return true if pointer type
     */
    bool isPointerType(clang::QualType Type) const;
};

#endif // MOVE_ASSIGNMENT_TRANSLATOR_H
