/**
 * @file MethodHandler.h
 * @brief Handler for processing C++ methods (instance and static) using dispatcher pattern
 *
 * Registers with CppToCVisitorDispatcher to handle C++ method declarations.
 * Translates C++ member functions (methods) to C free functions with explicit
 * "this" parameter for instance methods.
 *
 * NOTE: This is a unified handler that covers both instance and static methods.
 * It delegates to InstanceMethodHandler and StaticMethodHandler internally,
 * or can be used as a standalone handler for projects that don't need the split.
 *
 * Phase Migration: Converting from ASTHandler inheritance to dispatcher pattern
 * - Old: class MethodHandler : public ASTHandler
 * - New: class MethodHandler { static void registerWith(...) }
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
 * @class MethodHandler
 * @brief Processes CXXMethodDecl and creates C functions with explicit this parameter
 *
 * Responsibilities:
 * - Match CXXMethodDecl nodes (predicate) - both instance and static methods
 * - Exclude constructors and destructors (have dedicated handlers)
 * - Translate method signature (name, return type, parameters)
 * - For instance methods: Create explicit "this" parameter as FIRST parameter
 * - For static methods: No "this" parameter
 * - Apply name mangling via NameMangler API
 * - Create C FunctionDecl with translated signature
 * - Add translated function to appropriate C TranslationUnit
 *
 * Translation Examples:
 *
 * Instance Method:
 * C++: class Counter {
 *          void increment() { value++; }
 *      };
 *
 * C:   void Counter__increment(struct Counter* this) { this->value++; }
 *
 * Static Method:
 * C++: class Counter {
 *          static int getVersion() { return 1; }
 *      };
 *
 * C:   int Counter__getVersion(void) { return 1; }
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, ...);
 * MethodHandler::registerWith(dispatcher);
 *
 * CXXMethodDecl* method = ...;
 * dispatcher.dispatch(cppCtx, cCtx, method);
 * // → Creates C FunctionDecl with appropriate signature
 * @endcode
 */
class MethodHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for CXXMethodDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is a CXXMethodDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is CXXMethodDecl (excluding constructors/destructors)
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     * 3. Accept CXXMethod kind
     * 4. Exclude constructors and destructors
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ method to C function
     * @param disp Dispatcher for accessing PathMapper and child handlers
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D CXXMethodDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is CXXMethodDecl
     * 2. Cast D to CXXMethodDecl
     * 3. Check declMapper.hasCreated() - skip if already translated
     * 4. Compute mangled name using NameMangler API (cpptoc::mangle_method)
     * 5. Translate return type via TypeHandler
     * 6. For instance methods:
     *    - Create "this" parameter (struct ClassName* this)
     *    - Prepend to parameter list
     * 7. Translate method parameters
     * 8. Translate function body (if exists)
     * 9. Create C FunctionDecl
     * 10. Add to appropriate C TranslationUnit
     * 11. Register in DeclMapper and PathMapper
     *
     * @pre D != nullptr && D->getKind() == Decl::CXXMethod (asserted)
     */
    static void handleMethod(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Create "this" parameter for instance method
     * @param classDecl Parent class declaration
     * @param cASTContext Target C ASTContext
     * @return ParmVarDecl representing "struct ClassName* this"
     *
     * Creates: struct ClassName* this
     * For use as first parameter in translated instance method.
     */
    static clang::ParmVarDecl* createThisParameter(
        const clang::CXXRecordDecl* classDecl,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Translate method parameters by dispatching to child handlers
     * @param method C++ method declaration
     * @param disp Dispatcher for parameter translation
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @return Vector of C ParmVarDecl (created by child handlers)
     *
     * Follows Chain of Responsibility pattern: Dispatches each parameter
     * to appropriate handler, then retrieves created C parameters.
     */
    static std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::CXXMethodDecl* method,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
