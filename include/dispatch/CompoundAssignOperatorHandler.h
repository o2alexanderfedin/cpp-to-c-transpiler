/**
 * @file CompoundAssignOperatorHandler.h
 * @brief Handler for CompoundAssignOperator (+=, -=, *=, etc.)
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @class CompoundAssignOperatorHandler
 * @brief Handles compound assignment operators
 *
 * CompoundAssignOperator represents operators like +=, -=, *=, /=, etc.
 * These are valid in both C++ and C, so we preserve them.
 */
class CompoundAssignOperatorHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Stmt* S);

    static void handleCompoundAssignOperator(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
