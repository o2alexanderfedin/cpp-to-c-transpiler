/**
 * @file IfStmtHandler.h
 * @brief Handler for translating if statements
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

/**
 * @class IfStmtHandler
 * @brief Processes IfStmt and translates condition, then/else branches
 */
class IfStmtHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Check if statement is IfStmt
     */
    static bool canHandle(const clang::Stmt* S);

    /**
     * @brief Translate if statement by dispatching condition and branches
     */
    static void handleIfStmt(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
