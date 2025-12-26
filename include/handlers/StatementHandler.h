/**
 * @file StatementHandler.h
 * @brief Handler for translating C++ statements to C statements
 *
 * Translates C++ control flow and structural statements to their C equivalents.
 * Handles return statements, compound statements (blocks), and delegates to
 * other handlers for declarations and expressions.
 *
 * Scope (Phase 1 - Task 3):
 * - Return statements (void and with expressions)
 * - Compound statements (blocks)
 * - Statement recursion for nested structures
 *
 * Out of Scope (Later Phases):
 * - Control flow statements (if, while, for, switch) - Phase 2
 * - Declaration statements - Delegated to VariableHandler
 * - Expression statements - Delegated to ExpressionHandler
 * - Range-based for loops - Future phase
 * - Try-catch blocks - Future phase
 */

#pragma once

#include "handlers/ASTHandler.h"

namespace cpptoc {

/**
 * @class StatementHandler
 * @brief Translates C++ statements to C statements
 *
 * Example Translations:
 *
 * Return Void:
 *   C++: return;
 *   C:   return;
 *
 * Return Expression:
 *   C++: return x + y;
 *   C:   return x + y;
 *
 * Compound Statement:
 *   C++: { int x = 1; return x; }
 *   C:   { int x = 1; return x; }
 *
 * Nested Blocks:
 *   C++: { { return 42; } }
 *   C:   { { return 42; } }
 */
class StatementHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes statements
     */
    bool canHandle(const clang::Stmt* S) const override;

    /**
     * @brief Translate C++ statement to C statement
     * @param S C++ statement
     * @param ctx Handler context
     * @return C statement
     */
    clang::Stmt* handleStmt(const clang::Stmt* S, HandlerContext& ctx) override;

private:
    /**
     * @brief Translate return statement
     * @param RS C++ ReturnStmt
     * @param ctx Handler context
     * @return C ReturnStmt
     */
    clang::ReturnStmt* translateReturnStmt(
        const clang::ReturnStmt* RS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate compound statement (block)
     * @param CS C++ CompoundStmt
     * @param ctx Handler context
     * @return C CompoundStmt
     */
    clang::CompoundStmt* translateCompoundStmt(
        const clang::CompoundStmt* CS,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
