/**
 * @file StdMoveTranslator.h
 * @brief std::move() Call Detection and Translation to C (Story #132)
 *
 * Responsibilities (Single Responsibility Principle):
 * - Detect std::move() calls using Clang AST
 * - Analyze context: construction vs assignment vs argument vs return
 * - Generate appropriate C code based on context
 * - Integration with move constructor/assignment translators (Stories #130, #131)
 *
 * Design Principles:
 * - SOLID: Single responsibility, open for extension
 * - DRY: Reuse existing move constructor/assignment infrastructure
 * - KISS: Simple, clear API with context-based dispatch
 */

#ifndef STD_MOVE_TRANSLATOR_H
#define STD_MOVE_TRANSLATOR_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include <string>

class StdMoveTranslator {
public:
    /**
     * Move context - determines how std::move() is translated
     *
     * Different contexts require different C code generation:
     * - Construction: Buffer b2 = std::move(b1) → Buffer_move_construct(&b2, &b1)
     * - Assignment: b3 = std::move(b2) → Buffer_move_assign(&b3, &b2)
     * - Argument: func(std::move(obj)) → Buffer temp; Buffer_move_construct(&temp, &obj); func(&temp)
     * - Return: return std::move(local) → Buffer temp; Buffer_move_construct(&temp, &local); return temp
     */
    enum class MoveContext {
        Construction,  // Used in initialization/construction
        Assignment,    // Used in assignment expression
        Argument,      // Used as function argument
        Return         // Used in return statement
    };

    /**
     * Constructor
     * @param Context Clang AST context for type queries and traversal
     */
    explicit StdMoveTranslator(clang::ASTContext& Context);

    /**
     * Detect if expression is std::move() call
     *
     * Checks:
     * 1. Is it a CallExpr?
     * 2. Does it call a function named "move"?
     * 3. Is the function in the std namespace?
     *
     * @param Call Call expression to check
     * @return true if this is std::move() call
     */
    bool isStdMoveCall(const clang::CallExpr* Call) const;

    /**
     * Analyze context of std::move() call
     *
     * Examines parent AST nodes to determine usage:
     * - VarDecl with initializer → Construction
     * - BinaryOperator with = → Assignment
     * - CallExpr argument → Argument
     * - ReturnStmt → Return
     *
     * @param MoveCall std::move() call expression
     * @return Context classification
     */
    MoveContext analyzeMoveContext(const clang::CallExpr* MoveCall);

    /**
     * Generate C code for std::move() translation
     *
     * Delegates to appropriate translation method based on context:
     * - Construction → generateConstructionCode()
     * - Assignment → generateAssignmentCode()
     * - Argument → generateArgumentCode()
     * - Return → generateReturnCode()
     *
     * @param MoveCall std::move() call expression
     * @param Context Usage context
     * @return Generated C code
     */
    std::string translateStdMove(const clang::CallExpr* MoveCall, MoveContext Context);

private:
    clang::ASTContext& Context;

    /**
     * Extract argument from std::move(arg)
     *
     * std::move() takes one argument - the object to move.
     * This extracts that argument expression.
     *
     * @param MoveCall std::move() call expression
     * @return Argument expression (the object being moved)
     */
    const clang::Expr* getMovedArgument(const clang::CallExpr* MoveCall) const;

    /**
     * Get type name from expression
     *
     * Extracts the type of the expression and returns its name as a string.
     * Used to generate function names like "Buffer_move_construct".
     *
     * Example: For expression "obj" of type "Buffer", returns "Buffer"
     *
     * @param E Expression to analyze
     * @return Type name as string
     */
    std::string getTypeName(const clang::Expr* E) const;

    /**
     * Get variable name from expression
     *
     * Extracts the variable name if expression is a DeclRefExpr.
     * Used to generate code like "&obj" from "obj".
     *
     * @param E Expression to analyze
     * @return Variable name or empty string
     */
    std::string getVariableName(const clang::Expr* E) const;

    /**
     * Generate C code for construction context
     *
     * Pattern: Buffer b2 = std::move(b1);
     * Generated: Buffer_move_construct(&b2, &b1);
     *
     * @param MoveCall std::move() call expression
     * @return Generated C code
     */
    std::string generateConstructionCode(const clang::CallExpr* MoveCall);

    /**
     * Generate C code for assignment context
     *
     * Pattern: b3 = std::move(b2);
     * Generated: Buffer_move_assign(&b3, &b2);
     *
     * @param MoveCall std::move() call expression
     * @return Generated C code
     */
    std::string generateAssignmentCode(const clang::CallExpr* MoveCall);

    /**
     * Generate C code for function argument context
     *
     * Pattern: func(std::move(obj));
     * Generated: Buffer __arg_temp__;
     *            Buffer_move_construct(&__arg_temp__, &obj);
     *            func(&__arg_temp__);
     *
     * @param MoveCall std::move() call expression
     * @return Generated C code
     */
    std::string generateArgumentCode(const clang::CallExpr* MoveCall);

    /**
     * Generate C code for return statement context
     *
     * Pattern: return std::move(local);
     * Generated: Buffer __return_temp__;
     *            Buffer_move_construct(&__return_temp__, &local);
     *            return __return_temp__;
     *
     * @param MoveCall std::move() call expression
     * @return Generated C code
     */
    std::string generateReturnCode(const clang::CallExpr* MoveCall);

    /**
     * Find parent statement of given expression
     *
     * Traverses AST upward to find the enclosing statement.
     * Used for context analysis.
     *
     * @param E Expression to start from
     * @return Parent statement or nullptr
     */
    const clang::Stmt* findParentStmt(const clang::Expr* E) const;
};

#endif // STD_MOVE_TRANSLATOR_H
