/**
 * @file LiteralHandler.h
 * @brief Handler for literal expressions (integers, floats, strings, chars, bools)
 *
 * Implements Chain of Responsibility pattern for dispatching literal expressions.
 * Handles: IntegerLiteral, FloatingLiteral, StringLiteral, CharacterLiteral, CXXBoolLiteralExpr
 *
 * Design Principles:
 * - Single Responsibility: Only handles literal expression translation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"

namespace cpptoc {

/**
 * @class LiteralHandler
 * @brief Translates C++ literal expressions to C literal expressions
 *
 * Handles all literal types:
 * - IntegerLiteral (42, 0xFF, 0777, etc.)
 * - FloatingLiteral (3.14, 1.0e-5, etc.)
 * - StringLiteral ("hello", L"wide", etc.)
 * - CharacterLiteral ('a', '\n', etc.)
 * - CXXBoolLiteralExpr (true, false)
 *
 * Literals have no subexpressions, so no recursive dispatch needed.
 */
class LiteralHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if expression is a literal
     * @param E Expression to check
     * @return true if E is any literal type, false otherwise
     */
    static bool canHandle(const clang::Expr* E);

    /**
     * @brief Handle literal expression translation
     * @param disp Dispatcher (for accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param E Literal expression to translate
     *
     * Creates C literal node and stores in ExprMapper.
     */
    static void handleLiteral(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Expr* E
    );

private:
    // Code-by-intent: Separate creation function for each literal type
    static clang::Expr* createIntegerLiteral(
        const clang::IntegerLiteral* cppLit,
        clang::ASTContext& cASTContext
    );

    static clang::Expr* createFloatingLiteral(
        const clang::FloatingLiteral* cppLit,
        clang::ASTContext& cASTContext
    );

    static clang::Expr* createStringLiteral(
        const clang::StringLiteral* cppLit,
        clang::ASTContext& cASTContext
    );

    static clang::Expr* createCharacterLiteral(
        const clang::CharacterLiteral* cppLit,
        clang::ASTContext& cASTContext
    );

    static clang::Expr* createBoolLiteral(
        const clang::CXXBoolLiteralExpr* cppLit,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
