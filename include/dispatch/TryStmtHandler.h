/**
 * @file TryStmtHandler.h
 * @brief Handler for C++ try-catch statements (CXXTryStmt)
 *
 * Implements Chain of Responsibility pattern for dispatching try-catch statements.
 * Handles: CXXTryStmt (try-catch blocks)
 *
 * Design Principles:
 * - Single Responsibility: Only handles try-catch statement translation
 * - Delegation: Delegates to TryCatchTransformer service class for implementation
 * - Open/Closed: Extend via new handlers, don't modify existing
 * - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/StmtCXX.h"

namespace cpptoc {

/**
 * @class TryStmtHandler
 * @brief Translates C++ try-catch statements to C setjmp/longjmp control flow
 *
 * CXXTryStmt represents try-catch blocks:
 * - try { ... } catch (Error e) { ... }
 * - Nested try-catch blocks
 * - Multiple catch handlers
 *
 * Delegates to TryCatchTransformer service class for implementation.
 */
class TryStmtHandler {
public:
    /**
     * @brief Register handler with dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(::CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Predicate: Check if statement is a try-catch statement
     * @param S Statement to check
     * @return true if S is CXXTryStmt, false otherwise
     */
    static bool canHandle(const clang::Stmt* S);

    /**
     * @brief Handle try-catch statement translation
     * @param disp Dispatcher (for recursive dispatch and accessing mappers)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param S CXXTryStmt to translate
     *
     * Delegates to TryCatchTransformer to generate C code for:
     * 1. Exception frame setup
     * 2. setjmp guard
     * 3. Try body with frame push/pop
     * 4. Catch handlers with type matching
     */
    static void handleTryStmt(
        const ::CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Stmt* S
    );
};

} // namespace cpptoc
