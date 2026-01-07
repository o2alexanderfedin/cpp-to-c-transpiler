/**
 * @file StatementHandler.h
 * @brief Handler for processing various statement types not covered by specific handlers
 *
 * Registers with CppToCVisitorDispatcher to handle C++ statements.
 * Handles control flow statements (if, while, for, switch, etc.) that don't have
 * dedicated handlers yet.
 *
 * Note: ReturnStmt and CompoundStmt have their own dedicated handlers.
 * This handler covers:
 * - IfStmt (conditional statements)
 * - WhileStmt (while loops)
 * - DoStmt (do-while loops)
 * - ForStmt (for loops)
 * - SwitchStmt (switch statements)
 * - CaseStmt (case labels)
 * - DefaultStmt (default labels)
 * - BreakStmt (break statements)
 * - ContinueStmt (continue statements)
 * - GotoStmt (goto statements)
 * - LabelStmt (label statements)
 * - DeclStmt (declaration statements)
 * - CXXForRangeStmt (range-based for loops)
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"

namespace cpptoc {

/**
 * @class StatementHandler
 * @brief Processes various statement types and creates C equivalents
 *
 * Responsibilities:
 * - Match statement types not handled by dedicated handlers
 * - Translate control flow statements to C equivalents
 * - Recursively dispatch sub-statements via dispatcher
 * - Create C statement nodes and store in StmtMapper
 *
 * Translation Examples:
 *
 * If Statement:
 *   C++: if (x > 0) { ... } else { ... }
 *   C:   if (x > 0) { ... } else { ... }
 *
 * While Statement:
 *   C++: while (x > 0) { ... }
 *   C:   while (x > 0) { ... }
 *
 * Switch Statement:
 *   C++: switch (state) { case State::A: ...; break; }
 *   C:   switch (state) { case State__A: ...; break; }
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, ...);
 * StatementHandler::registerWith(dispatcher);
 *
 * Stmt* cppStmt = ...;
 * dispatcher.dispatch(cppCtx, cCtx, cppStmt);
 * // → Creates C Stmt and stores in StmtMapper
 * @endcode
 */
class StatementHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for various statement types
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if statement can be handled
     * @param S Statement to check (must not be null)
     * @return true if S is a statement type handled by this handler
     *
     * Returns true for:
     * - IfStmt, WhileStmt, DoStmt, ForStmt, CXXForRangeStmt
     * - SwitchStmt, CaseStmt, DefaultStmt
     * - BreakStmt, ContinueStmt
     * - GotoStmt, LabelStmt
     * - DeclStmt
     *
     * Returns false for:
     * - ReturnStmt (handled by ReturnStmtHandler)
     * - CompoundStmt (handled by CompoundStmtHandler)
     *
     * @pre S != nullptr (asserted)
     */
    static bool canHandle(const clang::Stmt* S);

    /**
     * @brief Visitor: Translate C++ statement to C statement
     * @param disp Dispatcher for recursive statement dispatch
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param S Statement to process (must not be null)
     *
     * Algorithm:
     * 1. Assert S is not null and is a handled statement type
     * 2. Check StmtMapper - skip if already translated
     * 3. Determine statement type and dispatch to appropriate helper
     * 4. Create C statement node
     * 5. Store in StmtMapper for parent retrieval
     *
     * @pre S != nullptr && canHandle(S) (asserted)
     */
    static void handleStatement(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );

    // Helper functions for specific statement types
    static clang::IfStmt* translateIfStmt(
        const clang::IfStmt* IS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::WhileStmt* translateWhileStmt(
        const clang::WhileStmt* WS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::DoStmt* translateDoStmt(
        const clang::DoStmt* DS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::ForStmt* translateForStmt(
        const clang::ForStmt* FS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::ForStmt* translateCXXForRangeStmt(
        const clang::CXXForRangeStmt* RFS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::SwitchStmt* translateSwitchStmt(
        const clang::SwitchStmt* SS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::CaseStmt* translateCaseStmt(
        const clang::CaseStmt* CS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::DefaultStmt* translateDefaultStmt(
        const clang::DefaultStmt* DS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::BreakStmt* translateBreakStmt(
        const clang::BreakStmt* BS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::ContinueStmt* translateContinueStmt(
        const clang::ContinueStmt* CS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::GotoStmt* translateGotoStmt(
        const clang::GotoStmt* GS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::LabelStmt* translateLabelStmt(
        const clang::LabelStmt* LS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    static clang::Stmt* translateDeclStmt(
        const clang::DeclStmt* DS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );
};

} // namespace cpptoc
