/**
 * @file FunctionHandler.h
 * @brief Handler for processing FunctionDecl nodes (free functions only)
 *
 * Registers with CppToCVisitorDispatcher to handle C++ free function declarations.
 * Translates function signatures (name, return type, parameters) to C equivalents.
 *
 * Phase 1 Scope: Signature translation ONLY
 * - Function name and return type
 * - Parameter translation (references → pointers)
 * - Function bodies set to nullptr (no statement translation yet)
 *
 * Future Phases:
 * - Statement/expression translation for function bodies
 * - Default parameters
 * - Inline functions
 * - Static functions
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"

namespace cpptoc {

/**
 * @class FunctionHandler
 * @brief Processes FunctionDecl and creates C function declarations
 *
 * Responsibilities:
 * - Match FunctionDecl nodes (predicate) - EXCLUDING CXXMethodDecl
 * - Translate function signature (name, return type, parameters)
 * - Convert C++ references to C pointers in signature
 * - Create C FunctionDecl with nullptr body (Phase 1 limitation)
 * - Add translated function to appropriate C TranslationUnit
 *
 * Translation Example:
 * C++:  int add(int a, const int& b) { return a + b; }
 * C:    int add(int a, const int* b);  // Body nullptr in Phase 1
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper);
 * FunctionHandler::registerWith(dispatcher);
 *
 * FunctionDecl* cppFunc = ...;
 * dispatcher.dispatch(cppCtx, cCtx, cppFunc);
 * // → Creates C FunctionDecl with signature only (no body)
 * @endcode
 */
class FunctionHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for FunctionDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY FunctionDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is FunctionDecl AND NOT CXXMethodDecl
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     * 3. Exclude CXXMethodDecl (methods handled separately)
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ function to C function
     * @param disp Dispatcher for accessing PathMapper
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D FunctionDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is FunctionDecl (not method)
     * 2. Cast D to FunctionDecl
     * 3. Extract function properties (name, return type, parameters)
     * 4. Translate return type (references → pointers)
     * 5. Translate each parameter (references → pointers)
     * 6. Create C FunctionDecl with translated signature
     * 7. Set body to nullptr (Phase 1: no statement translation)
     * 8. Get target path and C TranslationUnit
     * 9. Add C function to C TranslationUnit
     * 10. Register node location in PathMapper
     *
     * Phase 1 Limitation: Function body is nullptr
     * - Body translation requires StatementHandler (future phase)
     * - This phase focuses on declaration/signature translation
     *
     * @pre D != nullptr && D->getKind() == Decl::Function (asserted)
     */
    static void handleFunction(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Translate C++ type to C type (helper)
     * @param cppType C++ type
     * @param cASTContext Target C ASTContext
     * @return C type (with references converted to pointers)
     *
     * Translation rules:
     * - T& (lvalue reference) → T*
     * - T&& (rvalue reference) → T*
     * - const T& → const T*
     * - All other types → unchanged
     */
    static clang::QualType translateType(
        clang::QualType cppType,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Translate function parameters by dispatching to ParameterHandler
     * @param cppFunc C++ function declaration
     * @param disp Dispatcher for parameter translation
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @return Vector of C ParmVarDecl (created by ParameterHandler)
     *
     * Follows Chain of Responsibility pattern: Dispatches each parameter
     * to ParameterHandler, then retrieves created C parameters via PathMapper.
     */
    static std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::FunctionDecl* cppFunc,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
