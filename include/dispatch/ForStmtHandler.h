/**
 * @file ForStmtHandler.h
 * @brief Handler for ForStmt (for loops)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

/**
 * @class ForStmtHandler
 * @brief Translates C++ for loops to C
 *
 * ForStmt represents for loops. The structure is the same in C++ and C,
 * so translation is mostly straightforward, but we need to dispatch all
 * sub-components (init, condition, increment, body).
 */
class ForStmtHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Stmt* S);

    static void handleForStmt(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
