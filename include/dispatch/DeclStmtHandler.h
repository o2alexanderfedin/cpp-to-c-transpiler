/**
 * @file DeclStmtHandler.h
 * @brief Handler for declaration statements (DeclStmt)
 *
 * Implements Chain of Responsibility pattern for dispatching DeclStmt nodes.
 * A DeclStmt is a statement that contains one or more declarations, typically
 * local variable declarations within a function body.
 *
 * Design Principles:
 * - Single Responsibility: Only handles DeclStmt translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Delegation: Delegates to VariableHandler for actual variable translation
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

/**
 * @class DeclStmtHandler
 * @brief Translates declaration statements (DeclStmt) from C++ to C
 *
 * Handles declaration statements by:
 * 1. Detecting DeclStmt nodes
 * 2. Extracting all declarations from the statement
 * 3. Dispatching each declaration to appropriate handler (usually VariableHandler)
 * 4. Creating C DeclStmt with translated declarations
 * 5. Storing result in StmtMapper
 *
 * Example C++ code:
 * @code
 * int x = 5;       // DeclStmt containing VarDecl
 * int a, b = 3;    // DeclStmt containing multiple VarDecls
 * @endcode
 */
class DeclStmtHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if statement is a DeclStmt
     * @param S Statement to check
     * @return true if S is DeclStmt, false otherwise
     */
    static bool canHandle(const clang::Stmt* S);

    /**
     * @brief Handle DeclStmt translation
     * @param disp Dispatcher (for accessing mappers and recursive dispatch)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param S DeclStmt to translate
     *
     * Flow:
     * 1. Cast S to DeclStmt
     * 2. Check StmtMapper for existing translation (prevent duplication)
     * 3. Iterate through all declarations in the statement
     * 4. Dispatch each declaration to appropriate handler
     * 5. Create C DeclStmt with translated declarations
     * 6. Store C DeclStmt in StmtMapper
     */
    static void handleDeclStmt(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
