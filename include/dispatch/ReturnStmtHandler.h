/**
 * @file ReturnStmtHandler.h
 * @brief Handler for processing ReturnStmt nodes
 *
 * Registers with CppToCVisitorDispatcher to handle C++ return statements.
 * Translates return statement structure and return value expressions to C equivalents.
 *
 * Phase 1 Scope: Basic return statement translation
 * - Translate return statement structure (ReturnStmt AST nodes)
 * - Translate return value expressions (references → pointers via TypeTranslator)
 * - Create C ReturnStmt nodes with translated expressions
 * - NOT included in Phase 1: Complex expression translation (requires ExpressionHandler)
 *
 * Future Phases:
 * - Complex expression translation for return values
 * - Return value optimization (RVO/NRVO)
 * - Return type coercion
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

/**
 * @class ReturnStmtHandler
 * @brief Processes ReturnStmt and creates C return statements
 *
 * Responsibilities:
 * - Match ReturnStmt nodes (predicate)
 * - Translate return value expression type (references → pointers)
 * - Create C ReturnStmt with translated expression
 * - Handle void returns (return; with nullptr value)
 *
 * Translation Examples:
 * C++:  return 42;              → C: return 42;
 * C++:  return a + b;           → C: return a + b;
 * C++:  return someRef;         → C: return someRef; (type translated)
 * C++:  return;                 → C: return;
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, declMapper);
 * ReturnStmtHandler::registerWith(dispatcher);
 *
 * ReturnStmt* cppReturn = ...;
 * dispatcher.dispatch(cppCtx, cCtx, cppReturn);
 * // → Creates C ReturnStmt with translated type
 * @endcode
 */
class ReturnStmtHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for ReturnStmt
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if statement is EXACTLY ReturnStmt
     * @param S Statement to check (must not be null)
     * @return true if S is exactly ReturnStmt
     *
     * Implementation pattern:
     * 1. Assert S is not null (fails fast on programming errors)
     * 2. Use S->getStmtClass() for exact type matching
     *
     * @pre S != nullptr (asserted)
     */
    static bool canHandle(const clang::Stmt* S);

    /**
     * @brief Visitor: Translate C++ return statement to C return statement
     * @param disp Dispatcher for dispatching return value expression
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param S ReturnStmt to process (must not be null)
     *
     * Algorithm (following Chain of Responsibility pattern):
     * 1. Assert S is not null and is ReturnStmt
     * 2. Cast S to ReturnStmt
     * 3. Extract return value expression (may be nullptr for void return)
     * 4. If return value exists:
     *    a. Dispatch expression to ExpressionHandler via dispatcher
     *    b. If handled, retrieve translated C expression (requires ExprMapper - future)
     *    c. If not handled, use fallback (Phase 1: original expression)
     * 5. Create C ReturnStmt using clang::ReturnStmt::Create()
     * 6. Store mapping for parent handler retrieval
     *
     * Chain of Responsibility: Delegates expression translation to ExpressionHandler
     * - Similar to how FunctionHandler delegates parameters to ParameterHandler
     * - When ExpressionHandler exists, will retrieve translated expr from ExprMapper
     * - Phase 1: Falls back to original expression when no handler registered
     *
     * @pre S != nullptr && S->getStmtClass() == Stmt::ReturnStmtClass (asserted)
     */
    static void handleReturnStmt(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
