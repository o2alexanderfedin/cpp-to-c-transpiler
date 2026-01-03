#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @brief Handler for InitListExpr (array/struct initializers)
 * @details Pass-through handler that copies InitListExpr from C++ AST to C AST
 */
class InitListExprHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Check if this handler can handle the given expression
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle InitListExpr by passing it through
     */
    static void handleInitListExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
