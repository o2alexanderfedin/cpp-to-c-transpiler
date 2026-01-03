/**
 * @file VariableHandler.h
 * @brief Handler for processing VarDecl nodes (variable declarations)
 *
 * Registers with CppToCVisitorDispatcher to handle C++ variable declarations.
 * Translates C++ variables (local, global, static) to C variable declarations.
 *
 * Phase 1 Scope: Variable translation ONLY
 * - Global variables (TranslationUnitDecl scope)
 * - Local variables (within function scope)
 * - Static variables (file and function scope)
 * - Storage class translation (extern, static, register)
 * - Type translation (dispatch types via TypeHandler)
 * - Initialization expression handling
 *
 * Future Phases:
 * - Complex initialization expressions (Phase 2)
 * - Array variables (Phase 2)
 * - Constexpr variables (Phase 3)
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"

namespace cpptoc {

/**
 * @class VariableHandler
 * @brief Processes VarDecl and creates C variable declarations
 *
 * Responsibilities:
 * - Match VarDecl nodes (predicate) - excludes FieldDecl (handled by RecordHandler)
 * - Translate variable types via TypeHandler (reference → pointer)
 * - Translate storage class specifiers
 * - Translate initialization expressions (literals for now)
 * - Create C VarDecl with appropriate scope (global vs local)
 * - Add translated variable to appropriate DeclContext
 *
 * Translation Examples:
 *
 * C++ global variable:
 * @code
 * int globalCounter = 0;
 * @endcode
 *
 * C global variable (identical):
 * @code
 * int globalCounter = 0;
 * @endcode
 *
 * C++ static variable:
 * @code
 * static const int MAX = 100;
 * @endcode
 *
 * C static variable (identical):
 * @code
 * static const int MAX = 100;
 * @endcode
 *
 * C++ reference variable:
 * @code
 * int& ref = x;
 * @endcode
 *
 * C pointer variable:
 * @code
 * int* ref = &x;
 * @endcode
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, ...);
 * TypeHandler::registerWith(dispatcher);  // Must register before VariableHandler
 * VariableHandler::registerWith(dispatcher);
 *
 * VarDecl* cppVar = ...;
 * dispatcher.dispatch(cppCtx, cCtx, cppVar);
 * // → Creates C VarDecl with translated type
 * @endcode
 */
class VariableHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for VarDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY VarDecl (not FieldDecl)
     * @param D Declaration to check (must not be null)
     * @return true if D is VarDecl but NOT FieldDecl
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     * 3. Accept VarDecl but exclude FieldDecl (member variables)
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ variable to C variable
     * @param disp Dispatcher for accessing TypeMapper and PathMapper
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D VarDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is VarDecl
     * 2. Cast D to VarDecl
     * 3. Check declMapper.hasCreated() - skip if already translated
     * 4. Extract variable properties (name, type, storage class)
     * 5. Dispatch type via TypeHandler:
     *    - For reference types (T&, T&&): TypeHandler creates T*
     *    - For other types: pass through unchanged
     * 6. Retrieve translated type from TypeMapper
     * 7. Translate storage class:
     *    - SC_None → SC_None
     *    - SC_Static → SC_Static
     *    - SC_Extern → SC_Extern
     *    - SC_Auto → SC_None (implicit in C)
     *    - SC_Register → SC_Register
     * 8. Translate initialization expression (if present):
     *    - For Phase 1: Handle literal expressions only
     *    - Create equivalent literals in C ASTContext
     *    - For complex expressions: Future phase with ExpressionHandler
     * 9. Determine scope:
     *    - If parent is TranslationUnitDecl: global scope
     *    - Otherwise: Find translated parent function in DeclMapper
     * 10. Create C VarDecl with:
     *     - Appropriate DeclContext (global or local)
     *     - Translated type
     *     - Translated storage class
     *     - Translated initializer (if any)
     * 11. Add variable to DeclContext (makes it visible in AST)
     * 12. Store in declMapper
     * 13. Get target path and register location in PathMapper
     *
     * Phase 1 Limitation: Simple initialization only
     * - Only literal expressions supported
     * - Complex expressions require ExpressionHandler (future phase)
     *
     * @pre D != nullptr && D->getKind() == Decl::Var (asserted)
     */
    static void handleVariable(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Translate storage class specifier
     * @param sc C++ storage class
     * @return C storage class
     *
     * Mapping:
     * - SC_None → SC_None
     * - SC_Static → SC_Static
     * - SC_Extern → SC_Extern
     * - SC_Auto → SC_None (auto is implicit in C)
     * - SC_Register → SC_Register
     * - SC_PrivateExtern → SC_Static (Apple-specific)
     */
    static clang::StorageClass translateStorageClass(clang::StorageClass sc);

    /**
     * @brief Translate variable initialization expression
     * @param init C++ initialization expression
     * @param cASTContext Target C ASTContext (for creating C expressions)
     * @return C initialization expression, or nullptr if no init
     *
     * For Phase 1, handles literal expressions only:
     * - IntegerLiteral
     * - FloatingLiteral
     * - CharacterLiteral
     * - StringLiteral
     *
     * Creates equivalent literals in C ASTContext.
     * Phase 2 will handle complex expressions via ExpressionHandler.
     */
    static clang::Expr* translateInitializer(
        const clang::Expr* init,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
