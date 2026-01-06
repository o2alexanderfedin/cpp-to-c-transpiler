/**
 * @file ParameterHandler.h
 * @brief Handler for processing ParmVarDecl nodes (function parameters)
 *
 * Registers with CppToCVisitorDispatcher to handle C++ parameter declarations.
 * Translates parameter types (references → pointers) and creates C parameter declarations.
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"

namespace cpptoc {

/**
 * @class ParameterHandler
 * @brief Processes ParmVarDecl and creates C parameter declarations
 *
 * Responsibilities:
 * - Match ParmVarDecl nodes (predicate)
 * - Translate parameter type (references → pointers)
 * - Create C ParmVarDecl with translated type
 *
 * Translation Example:
 * C++:  const int& param
 * C:    const int* param
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper);
 * ParameterHandler::registerWith(dispatcher);
 *
 * ParmVarDecl* cppParam = ...;
 * clang::Decl* cParam = dispatcher.dispatch(cppCtx, cCtx, cppParam);
 * @endcode
 */
class ParameterHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for ParmVarDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY ParmVarDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is exactly ParmVarDecl
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ parameter to C parameter
     * @param disp Dispatcher (unused for parameters, but maintains signature consistency)
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D ParmVarDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is ParmVarDecl
     * 2. Cast D to ParmVarDecl
     * 3. Extract parameter name
     * 4. Translate parameter type (references → pointers)
     * 5. Create C ParmVarDecl with translated type
     * 6. Return C ParmVarDecl
     *
     * @pre D != nullptr && D->getKind() == Decl::ParmVar (asserted)
     */
    static void handleParameter(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );
};

} // namespace cpptoc
