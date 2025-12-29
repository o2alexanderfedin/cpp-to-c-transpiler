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
     * @brief Helper: Get source file path from TranslationUnit
     * @param cppASTContext C++ ASTContext containing SourceManager
     * @return Source file path (absolute path or "<stdin>" for in-memory sources)
     *
     * Implementation:
     * - Get main FileID from SourceManager
     * - Get FileEntry for main file
     * - Extract real path name
     * - Fallback to "<stdin>" for in-memory sources
     */
    static std::string getSourceFilePath(const clang::ASTContext& cppASTContext);

    /**
     * @brief Predicate: Check if declaration is EXACTLY TranslationUnitDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is exactly TranslationUnitDecl (not derived types)
     *
     * Implementation pattern for all handlers:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching (not isa<>)
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Process TranslationUnit and dispatch child declarations
     * @param disp Dispatcher for recursive dispatch
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D TranslationUnitDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is TranslationUnitDecl
     * 2. Cast D to TranslationUnitDecl
     * 3. Iterate all top-level declarations: TU->decls()
     * 4. For each child declaration:
     *    - Recursively dispatch: disp.dispatch(cppASTContext, cASTContext, child)
     * 5. Handler for child will create C AST nodes in cASTContext
     *
     * @pre D != nullptr && D->getKind() == Decl::TranslationUnit (asserted)
     */
    static void handleTranslationUnit(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );
};

} // namespace cpptoc
