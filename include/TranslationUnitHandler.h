/**
 * @file TranslationUnitHandler.h
 * @brief Handler for processing TranslationUnitDecl nodes
 *
 * Registers with CppToCVisitorDispatcher to handle top-level translation units.
 * Recursively dispatches all top-level declarations to appropriate handlers.
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "CppToCVisitorDispatcher.h"
#include "PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"

namespace cpptoc {

/**
 * @class TranslationUnitHandler
 * @brief Processes TranslationUnitDecl and dispatches child declarations
 *
 * Responsibilities:
 * - Match TranslationUnitDecl nodes (predicate)
 * - Iterate all top-level declarations
 * - Recursively dispatch each declaration through dispatcher
 * - Track which source file this TU represents
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper);
 * TranslationUnitHandler::registerWith(dispatcher);
 *
 * TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
 * dispatcher.dispatch(cppCtx, cCtx, TU);
 * @endcode
 */
class TranslationUnitHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for TranslationUnitDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY TranslationUnitDecl
     * @param D Declaration to check
     * @return true if D is exactly TranslationUnitDecl (not derived types)
     *
     * Implementation uses D->getKind() for exact type matching.
     * This is the recommended pattern for all handlers to ensure type safety.
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Process TranslationUnit and dispatch child declarations
     * @param disp Dispatcher for recursive dispatch
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D TranslationUnitDecl to process
     *
     * Algorithm:
     * 1. Cast D to TranslationUnitDecl
     * 2. Iterate all top-level declarations: TU->decls()
     * 3. For each child declaration:
     *    - Recursively dispatch: disp.dispatch(cppASTContext, cASTContext, child)
     * 4. Handler for child will create C AST nodes in cASTContext
     */
    static void handleTranslationUnit(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );
};

} // namespace cpptoc
