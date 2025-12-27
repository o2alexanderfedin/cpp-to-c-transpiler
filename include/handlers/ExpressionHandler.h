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

    /**
     * @brief Detect if a method call is virtual
     * @param MCE C++ CXXMemberCallExpr
     * @return true if the method is virtual, false otherwise
     *
     * Checks if the method being called through the CXXMemberCallExpr
     * is a virtual method. This is useful for translation logic that needs
     * to distinguish between virtual and non-virtual method calls.
     *
     * Virtual methods require dynamic dispatch in C through function pointers
     * or vtable lookups, while non-virtual methods can be direct calls.
     *
     * Returns false if:
     * - MCE is nullptr
     * - Method declaration cannot be retrieved
     * - Method is not virtual
     *
     * Returns true if:
     * - Method is declared with 'virtual' keyword
     * - Method overrides a virtual method from base class
     * - Method is a virtual destructor
     *
     * Examples:
     * virtual void process() { }      → isVirtualCall() returns true
     * void process() { }               → isVirtualCall() returns false
     * virtual ~Base() { }              → isVirtualCall() returns true
     */
    bool isVirtualCall(const clang::CXXMemberCallExpr* MCE) const;

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

    /**
     * @brief Translate CXXThisExpr (C++ 'this' keyword) to C DeclRefExpr
     * @param TE C++ CXXThisExpr
     * @param ctx Handler context
     * @return C DeclRefExpr referring to 'this' parameter
     *
     * Translates C++ 'this' keyword to a reference to the 'this' parameter
     * that was added by MethodHandler/ConstructorHandler/DestructorHandler.
     *
     * Example:
     * C++: this->field = 42;
     * C:   this->field = 42;  (where 'this' is a parameter)
     *
     * The type should be: struct ClassName* this
     */
    clang::Expr* translateCXXThisExpr(
        const clang::CXXThisExpr* TE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate CXXMemberCallExpr (C++ method call) to C function call
     * @param MCE C++ CXXMemberCallExpr
     * @param ctx Handler context
     * @return C CallExpr with explicit 'this' parameter
     *
     * Translates C++ method calls to C function calls with explicit object parameter.
     *
     * Translation rules:
     * - obj.method(args...) → ClassName_method(&obj, args...)
     * - ptr->method(args...) → ClassName_method(ptr, args...)
     * - this->method(args...) → ClassName_method(this, args...)
     *
     * The method must be registered in context via ctx.registerMethod().
     * If method is not found, returns nullptr.
     *
     * Examples:
     * C++: counter.increment();
     * C:   Counter_increment(&counter);
     *
     * C++: ptr->getValue();
     * C:   Counter_getValue(ptr);
     *
     * C++: this->helper(42);
     * C:   Counter_helper(this, 42);
     */
    clang::Expr* translateCXXMemberCallExpr(
        const clang::CXXMemberCallExpr* MCE,
        HandlerContext& ctx
    );

    /**
     * @brief Translate virtual method call to COM-style vtable dispatch (Phase 45 Task 7)
     * @param MCE C++ CXXMemberCallExpr (virtual call)
     * @param method Method being called
     * @param ctx Handler context
     * @return C CallExpr using vtable dispatch
     *
     * Translates virtual calls to COM/DCOM style vtable dispatch.
     * Pattern: obj->lpVtbl->methodName(obj, args...)
     *
     * Translation rules:
     * - ptr->draw() → ptr->lpVtbl->draw(ptr)
     * - obj.draw() → (&obj)->lpVtbl->draw(&obj)
     * - ref.draw() → ref->lpVtbl->draw(ref)  [ref becomes pointer in C]
     *
     * Examples:
     * C++: shape->draw();
     * C:   shape->lpVtbl->draw(shape);
     *
     * C++: shape->setColor(255, 128);
     * C:   shape->lpVtbl->setColor(shape, 255, 128);
     */
    clang::Expr* translateVirtualCall(
        const clang::CXXMemberCallExpr* MCE,
        const clang::CXXMethodDecl* method,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
