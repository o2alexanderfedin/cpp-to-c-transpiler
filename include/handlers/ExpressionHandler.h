/**
 * @file ExpressionHandler.h
 * @brief Handler for translating C++ expressions to C expressions
 *
 * Translates C++ expressions into their C equivalents. This includes:
 * - Literals (integer, floating, string, character)
 * - Binary operations (arithmetic, comparison, logical)
 * - Unary operations (prefix/postfix increment/decrement, unary minus/plus, logical not)
 * - Variable references (DeclRefExpr)
 * - Parenthesized expressions
 *
 * Scope (Phase 1):
 * - Basic expressions with literals and operators
 * - Variable references
 * - Arithmetic and logical operations
 * - Recursive translation of nested expressions
 *
 * Out of Scope (Future):
 * - Function calls (requires FunctionHandler coordination)
 * - Member access (requires ClassHandler coordination)
 * - Array subscripts
 * - Casts (static_cast, etc.)
 * - References (handled by reference translation layer)
 */

#pragma once

#include "handlers/ASTHandler.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @class ExpressionHandler
 * @brief Translates C++ expressions to C expressions
 *
 * Example Translations:
 * C++: 42                    → C: 42
 * C++: a + b                 → C: a + b
 * C++: (a + b) * c           → C: (a + b) * c
 * C++: -x                    → C: -x
 * C++: a > b && c < d        → C: a > b && c < d
 *
 * The handler recursively translates expression trees, preserving
 * operator precedence and structure.
 */
class ExpressionHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes expressions
     */
    bool canHandle(const clang::Expr* E) const override;

    /**
     * @brief Translate C++ expression to C expression
     * @param E C++ Expr
     * @param ctx Handler context
     * @return C Expr
     */
    clang::Expr* handleExpr(const clang::Expr* E, HandlerContext& ctx) override;

private:
    /**
     * @brief Translate integer literal
     */
    clang::Expr* translateIntegerLiteral(
        const clang::IntegerLiteral* IL,
        HandlerContext& ctx
    );

    /**
     * @brief Translate floating literal
     */
    clang::Expr* translateFloatingLiteral(
        const clang::FloatingLiteral* FL,
        HandlerContext& ctx
    );

    /**
     * @brief Translate string literal
     */
    clang::Expr* translateStringLiteral(
        const clang::StringLiteral* SL,
        HandlerContext& ctx
    );

    /**
     * @brief Translate character literal
     */
    clang::Expr* translateCharacterLiteral(
        const clang::CharacterLiteral* CL,
        HandlerContext& ctx
    );

    /**
     * @brief Translate binary operator
     */
    clang::Expr* translateBinaryOperator(
        const clang::BinaryOperator* BO,
        HandlerContext& ctx
    );

    /**
     * @brief Translate unary operator
     */
    clang::Expr* translateUnaryOperator(
        const clang::UnaryOperator* UO,
        HandlerContext& ctx
    );

    /**
     * @brief Translate declaration reference (variable reference)
     */
    clang::Expr* translateDeclRefExpr(
        const clang::DeclRefExpr* DRE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate parenthesized expression
     */
    clang::Expr* translateParenExpr(
        const clang::ParenExpr* PE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate implicit cast expression
     */
    clang::Expr* translateImplicitCastExpr(
        const clang::ImplicitCastExpr* ICE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate array subscript expression
     */
    clang::Expr* translateArraySubscriptExpr(
        const clang::ArraySubscriptExpr* ASE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate initializer list expression (array initialization)
     */
    clang::Expr* translateInitListExpr(
        const clang::InitListExpr* ILE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate C-style cast expression
     */
    clang::Expr* translateCStyleCastExpr(
        const clang::CStyleCastExpr* CCE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate nullptr literal (C++11) to NULL (C)
     */
    clang::Expr* translateNullPtrLiteral(
        const clang::CXXNullPtrLiteralExpr* NPE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate member expression (field access with . or ->)
     */
    clang::Expr* translateMemberExpr(
        const clang::MemberExpr* ME,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
