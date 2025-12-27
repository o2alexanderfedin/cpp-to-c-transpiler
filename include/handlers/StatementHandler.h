/**
 * @file StatementHandler.h
 * @brief Handler for translating C++ statements to C statements
 *
 * Translates C++ control flow and structural statements to their C equivalents.
 * Handles return statements, compound statements (blocks), and delegates to
 * other handlers for declarations and expressions.
 *
 * Scope (Phase 1 - Task 3):
 * - Return statements (void and with expressions)
 * - Compound statements (blocks)
 * - Statement recursion for nested structures
 *
 * Out of Scope (Later Phases):
 * - Control flow statements (if, while, for, switch) - Phase 2
 * - Declaration statements - Delegated to VariableHandler
 * - Expression statements - Delegated to ExpressionHandler
 * - Range-based for loops - Future phase
 * - Try-catch blocks - Future phase
 */

#pragma once

#include "handlers/ASTHandler.h"
#include "clang/AST/StmtCXX.h"

namespace cpptoc {

/**
 * @class StatementHandler
 * @brief Translates C++ statements to C statements
 *
 * Example Translations:
 *
 * Return Void:
 *   C++: return;
 *   C:   return;
 *
 * Return Expression:
 *   C++: return x + y;
 *   C:   return x + y;
 *
 * Compound Statement:
 *   C++: { int x = 1; return x; }
 *   C:   { int x = 1; return x; }
 *
 * Nested Blocks:
 *   C++: { { return 42; } }
 *   C:   { { return 42; } }
 */
class StatementHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes statements
     */
    bool canHandle(const clang::Stmt* S) const override;

    /**
     * @brief Translate C++ statement to C statement
     * @param S C++ statement
     * @param ctx Handler context
     * @return C statement
     */
    clang::Stmt* handleStmt(const clang::Stmt* S, HandlerContext& ctx) override;

private:
    /**
     * @brief Translate return statement
     * @param RS C++ ReturnStmt
     * @param ctx Handler context
     * @return C ReturnStmt
     */
    clang::ReturnStmt* translateReturnStmt(
        const clang::ReturnStmt* RS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate compound statement (block)
     * @param CS C++ CompoundStmt
     * @param ctx Handler context
     * @return C CompoundStmt
     */
    clang::CompoundStmt* translateCompoundStmt(
        const clang::CompoundStmt* CS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate if statement
     * @param IS C++ IfStmt
     * @param ctx Handler context
     * @return C IfStmt
     */
    clang::IfStmt* translateIfStmt(
        const clang::IfStmt* IS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate while statement
     * @param WS C++ WhileStmt
     * @param ctx Handler context
     * @return C WhileStmt
     */
    clang::WhileStmt* translateWhileStmt(
        const clang::WhileStmt* WS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate switch statement
     * @param SS C++ SwitchStmt
     * @param ctx Handler context
     * @return C SwitchStmt
     */
    clang::SwitchStmt* translateSwitchStmt(
        const clang::SwitchStmt* SS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate case statement
     * @param CS C++ CaseStmt
     * @param ctx Handler context
     * @return C CaseStmt
     */
    clang::CaseStmt* translateCaseStmt(
        const clang::CaseStmt* CS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate default statement
     * @param DS C++ DefaultStmt
     * @param ctx Handler context
     * @return C DefaultStmt
     */
    clang::DefaultStmt* translateDefaultStmt(
        const clang::DefaultStmt* DS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate break statement
     * @param BS C++ BreakStmt
     * @param ctx Handler context
     * @return C BreakStmt
     */
    clang::BreakStmt* translateBreakStmt(
        const clang::BreakStmt* BS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate continue statement
     * @param CS C++ ContinueStmt
     * @param ctx Handler context
     * @return C ContinueStmt
     */
    clang::ContinueStmt* translateContinueStmt(
        const clang::ContinueStmt* CS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate do-while statement
     * @param DS C++ DoStmt
     * @param ctx Handler context
     * @return C DoStmt
     */
    clang::DoStmt* translateDoStmt(
        const clang::DoStmt* DS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate for statement
     * @param FS C++ ForStmt
     * @param ctx Handler context
     * @return C ForStmt
     */
    clang::ForStmt* translateForStmt(
        const clang::ForStmt* FS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate range-based for statement (Phase 54)
     * @param RFS C++ CXXForRangeStmt
     * @param ctx Handler context
     * @return C ForStmt (index-based for arrays, iterator-based for containers)
     *
     * Translates range-based for loops to traditional C for loops:
     * - C arrays: Index-based loop (for (size_t i = 0; i < N; ++i))
     * - Containers: Iterator-based loop (deferred to future implementation)
     */
    clang::ForStmt* translateCXXForRangeStmt(
        const clang::CXXForRangeStmt* RFS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate goto statement
     * @param GS C++ GotoStmt
     * @param ctx Handler context
     * @return C GotoStmt
     */
    clang::GotoStmt* translateGotoStmt(
        const clang::GotoStmt* GS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate label statement
     * @param LS C++ LabelStmt
     * @param ctx Handler context
     * @return C LabelStmt
     */
    clang::LabelStmt* translateLabelStmt(
        const clang::LabelStmt* LS,
        HandlerContext& ctx
    );

    /**
     * @brief Translate declaration statement
     * @param DS C++ DeclStmt
     * @param ctx Handler context
     * @return C statement (may be CompoundStmt for object construction)
     *
     * Handles variable declarations, including:
     * - Simple variable declarations (int x;)
     * - Object declarations with automatic constructor/destructor calls
     *
     * For objects with class type:
     *   C++: MyClass obj(1, 2);
     *   C:   struct MyClass obj; MyClass_init_int_int(&obj, 1, 2);
     *
     * Returns CompoundStmt containing:
     *   1. Variable declaration (without initializer)
     *   2. Constructor call (if needed)
     */
    clang::Stmt* translateDeclStmt(
        const clang::DeclStmt* DS,
        HandlerContext& ctx
    );

    /**
     * @brief Helper to check if type is a class type requiring constructor call
     */
    bool isClassTypeRequiringConstructor(clang::QualType type);

    /**
     * @brief Helper to create constructor call for object
     * @param cppVarDecl The C++ variable declaration
     * @param cVarDecl The C variable declaration
     * @param ctx Handler context
     * @return Constructor call expression, or nullptr if not needed
     */
    clang::Expr* createConstructorCall(
        const clang::VarDecl* cppVarDecl,
        clang::VarDecl* cVarDecl,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
