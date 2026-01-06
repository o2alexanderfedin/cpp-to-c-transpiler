/**
 * @file SwitchStmtHandler.h
 * @brief Handler for SwitchStmt (switch statements)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

class SwitchStmtHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Stmt* S);

    static void handleSwitchStmt(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
