/**
 * @file CompoundAssignOperatorHandler.h
 * @brief Handler for compound assignment operator expressions (+=, -=, *=, /=, %=, etc.)
 *
 * Implements Chain of Responsibility pattern for dispatching CompoundAssignOperator nodes.
 * Handles: Compound assignments by translating them to regular assignments with binary operations
 *
 * Design Principles:
 * - Single Responsibility: Only handles compound assignment operator translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 * - Recursive Dispatch: Dispatches LHS and RHS subexpressions through dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class CompoundAssignOperatorHandler
 * @brief Translates C++ compound assignment operators to C simple assignments
 *
 * Handles all compound assignment operators:
 * - Arithmetic: +=, -=, *=, /=, %=
 * - Bitwise: &=, |=, ^=, <<=, >>=
 *
 * Translation strategy:
 * - C++ code: x += 5
 * - C code: x = x + 5
 *
 * CRITICAL: Uses recursive dispatch pattern:
 * 1. Extract LHS and RHS subexpressions
 * 2. Dispatch LHS via dispatcher (recursive)
 * 3. Dispatch RHS via dispatcher (recursive)
 * 4. Retrieve translated LHS from ExprMapper
 * 5. Retrieve translated RHS from ExprMapper
 * 6. Create C BinaryOperator for the operation (e.g., + for +=)
 * 7. Create C BinaryOperator for assignment (=) with LHS and the operation result
 * 8. Store in ExprMapper
 */
class CompoundAssignOperatorHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a CompoundAssignOperator
     * @param E Expression to check
     * @return true if E is CompoundAssignOperator, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle CompoundAssignOperator translation with recursive dispatch
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E CompoundAssignOperator to translate
     *
     * Recursively dispatches LHS and RHS, then creates C assignment with binary operation.
     */
    static void handleCompoundAssignOperator(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );

private:
    /**
     * @brief Convert compound assignment opcode to corresponding binary opcode
     * @param compoundOp Compound assignment opcode (e.g., BO_AddAssign)
     * @return Corresponding binary opcode (e.g., BO_Add)
     *
     * Examples:
     * - BO_AddAssign -> BO_Add
     * - BO_SubAssign -> BO_Sub
     * - BO_MulAssign -> BO_Mul
     */
    static clang::BinaryOperatorKind convertToBinaryOp(clang::BinaryOperatorKind compoundOp);
};

} // namespace cpptoc
