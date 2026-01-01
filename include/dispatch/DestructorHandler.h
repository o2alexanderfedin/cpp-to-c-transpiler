/**
 * @file DestructorHandler.h
 * @brief Handler for processing CXXDestructorDecl nodes
 *
 * Registers with CppToCVisitorDispatcher to handle C++ destructor declarations.
 * Translates C++ destructors to C cleanup functions with explicit this parameter.
 *
 * Scope (Phase 44):
 * - Simple destructors with cleanup code
 * - Virtual destructors (ignore virtual keyword for now)
 * - Destructor bodies (delegated to StatementHandler/ExpressionHandler)
 *
 * Future Phases:
 * - Virtual destructor tables (Phase 45 - Inheritance)
 * - Destructor call injection (handled by StatementHandler)
 * - Base class destructor chaining (Phase 45 - Inheritance)
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"

namespace cpptoc {

/**
 * @class DestructorHandler
 * @brief Processes CXXDestructorDecl and creates C cleanup functions
 *
 * Responsibilities:
 * - Match CXXDestructorDecl nodes (predicate)
 * - Translate destructor to C function with explicit this parameter
 * - Use cpptoc::mangle_destructor() for function naming
 * - Create C FunctionDecl with void return type
 * - Add translated function to appropriate C TranslationUnit
 *
 * Translation Examples:
 *
 * C++ destructor:
 * @code
 * class Counter {
 *     int count;
 * public:
 *     ~Counter() { count = 0; }
 * };
 * @endcode
 *
 * C cleanup function:
 * @code
 * struct Counter {
 *     int count;
 * };
 * void Counter_destroy(struct Counter* this) {
 *     this->count = 0;
 * }
 * @endcode
 *
 * Virtual destructor (Phase 44):
 * @code
 * class Base {
 * public:
 *     virtual ~Base() { }
 * };
 * @endcode
 *
 * C cleanup function (virtual keyword ignored):
 * @code
 * struct Base {
 *     // lpVtbl field added by RecordHandler
 * };
 * void Base_destroy(struct Base* this) {
 *     // empty body
 * }
 * @endcode
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, ...);
 * DestructorHandler::registerWith(dispatcher);
 *
 * CXXDestructorDecl* cppDtor = ...;
 * dispatcher.dispatch(cppCtx, cCtx, cppDtor);
 * // → Creates C FunctionDecl: ClassName_destroy(struct ClassName* this)
 * @endcode
 */
class DestructorHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for CXXDestructorDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY CXXDestructorDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is CXXDestructorDecl
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use llvm::isa<> for type checking
     * 3. Accept only CXXDestructorDecl
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ destructor to C cleanup function
     * @param disp Dispatcher for accessing PathMapper and child handlers
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D CXXDestructorDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is CXXDestructorDecl
     * 2. Cast D to CXXDestructorDecl
     * 3. Check DeclMapper.hasCreated() - skip if already translated
     * 4. Extract parent class (CXXRecordDecl)
     * 5. Generate function name using cpptoc::mangle_destructor()
     * 6. Find C struct (created by RecordHandler) in C TranslationUnit
     * 7. Create this parameter: struct ClassName* this
     * 8. Set return type: void
     * 9. Translate destructor body (if exists) via CompoundStmtHandler
     * 10. Create C FunctionDecl with translated signature and body
     * 11. Store in DeclMapper
     * 12. Get target path and C TranslationUnit
     * 13. Add C function to C TranslationUnit
     * 14. Register node location in PathMapper
     *
     * Phase 44 Limitation: Virtual keyword ignored
     * - Virtual destructors translated as regular functions
     * - Phase 45 will add vtable support for virtual destructors
     *
     * @pre D != nullptr && isa<CXXDestructorDecl>(D) (asserted)
     */
    static void handleDestructor(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Create this parameter for destructor function
     * @param recordType Type of the C struct (NOT C++ class)
     * @param cASTContext Target C ASTContext
     * @return ParmVarDecl for this parameter (struct ClassName* this)
     *
     * Creates: struct ClassName* this
     *
     * IMPORTANT: recordType must be from C ASTContext, not C++ ASTContext
     * Pattern (matching ConstructorHandler):
     * 1. Create pointer type from record type
     * 2. Get "this" identifier
     * 3. Create ParmVarDecl with SC_None storage class
     */
    static clang::ParmVarDecl* createThisParameter(
        clang::QualType recordType,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
