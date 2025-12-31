/**
 * @file CompoundStmtHandler.h
 * @brief Handler for compound statements (function bodies, block scopes)
 *
 * Implements Chain of Responsibility pattern for dispatching compound statements.
 * Handles: CompoundStmt (blocks of statements enclosed in braces)
 *
 * Design Principles:
 * - Single Responsibility: Only handles compound statement translation
 * - Recursive Dispatch: Dispatches each statement in the body via dispatcher
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class CompoundStmtHandler
 * @brief Translates C++ compound statements to C compound statements
 *
 * CompoundStmt represents a block of statements enclosed in braces:
 * - Function bodies: { stmt1; stmt2; ... }
 * - Block scopes: if (x) { ... }
 * - Loop bodies: while (x) { ... }
 *
 * Critical for function body translation - dispatches each statement
 * in the compound statement recursively.
 */
class CompoundStmtHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if statement is a compound statement
     * @param S Statement to check
     * @return true if S is CompoundStmt, false otherwise
     */
    static bool canHandle(const clang::Stmt* S);

    /**
     * @brief Handle compound statement translation
     * @param disp Dispatcher (for recursive dispatch and accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param S CompoundStmt to translate
     *
     * Recursively dispatches each statement in the body, retrieves from StmtMapper (future),
     * creates C CompoundStmt with translated statements, stores in StmtMapper.
     */
    static void handleCompoundStmt(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
