/**
 * @file WhileStmtHandler.h
 * @brief Handler for WhileStmt (while loops)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

/**
 * @class WhileStmtHandler
 * @brief Handles while loop statements
 *
 * WhileStmt represents while loops: while (condition) { body }
 * These are valid in both C++ and C, so we preserve them with translated parts.
 */
class WhileStmtHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Stmt* S);

    static void handleWhileStmt(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
