/**
 * @file CXXConstructExprHandler.h
 * @brief Handler for translating C++ constructor expressions to C struct initialization
 *
 * Registers with CppToCVisitorDispatcher to handle CXXConstructExpr nodes.
 * Translates C++ constructor calls in expressions to C99 compound literals.
 *
 * Example Translation:
 * C++: Vector3D(x, y, z)
 * C:   (struct Vector3D){x, y, z}
 *
 * C++: return Vector3D(1.0f, 2.0f, 3.0f);
 * C:   return (struct Vector3D){1.0f, 2.0f, 3.0f};
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class CXXConstructExprHandler
 * @brief Processes CXXConstructExpr and creates C compound literals
 *
 * Handles constructor call expressions (not constructor declarations).
 * Converts C++ class construction to C99 struct initialization.
 */
class CXXConstructExprHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if expression is CXXConstructExpr
     * @param E Expression to check (must not be null)
     * @return true if E is CXXConstructExpr
     *
     * @pre E != nullptr (asserted)
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Visitor: Translate C++ constructor expression to C compound literal
     * @param disp Dispatcher for accessing mappers and child handlers
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param E CXXConstructExpr to process (must not be null)
     *
     * Translation process:
     * 1. Recursively dispatch and translate all constructor arguments
     * 2. Look up C struct type from DeclMapper (C++ class -> C struct)
     * 3. Create InitListExpr with translated arguments
     * 4. Wrap in CompoundLiteralExpr to produce C99 syntax
     * 5. Store mapping in ExprMapper
     *
     * @pre E != nullptr && isa<CXXConstructExpr>(E) (asserted)
     */
    static void handleCXXConstructExpr(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );
};

} // namespace cpptoc
