/**
 * @file StaticMethodHandler.h
 * @brief Handler for processing static CXXMethodDecl nodes (static methods only)
 *
 * Registers with CppToCVisitorDispatcher to handle C++ static method declarations.
 * Translates static methods to C free functions with class name prefixing.
 *
 * Phase 1 Scope: Static method signature translation
 * - Static method name with class/namespace prefix (Class__method)
 * - Return type and parameter translation
 * - NO "this" parameter (static methods are class-scoped free functions)
 * - Function bodies translated via CompoundStmtHandler
 *
 * Future Phases:
 * - Static method overloading resolution
 * - Template static methods
 * - Static method inline optimization
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
 * @class StaticMethodHandler
 * @brief Processes static CXXMethodDecl and creates C function declarations
 *
 * Responsibilities:
 * - Match static CXXMethodDecl nodes (predicate) - EXCLUDING constructors/destructors
 * - Translate static method signature (name, return type, parameters)
 * - Apply class name prefix with __ separator (Class::method → Class__method)
 * - Apply namespace prefix if class is in namespace (NS::Class::method → NS__Class__method)
 * - Convert C++ references to C pointers in signature
 * - Create C FunctionDecl with translated signature and body
 * - Add translated function to appropriate C TranslationUnit
 *
 * Translation Example:
 * C++:  class Counter { public: static int getValue(); };
 *       int Counter::getValue() { return 42; }
 * C:    int Counter__getValue();
 *       int Counter__getValue() { return 42; }
 *
 * Namespace Example:
 * C++:  namespace game { class Entity { public: static int getMax(); }; }
 *       int game::Entity::getMax() { return 1000; }
 * C:    int game__Entity__getMax();
 *       int game__Entity__getMax() { return 1000; }
 *
 * Key Differences from Instance Methods:
 * - NO "this" parameter (static methods don't have instance context)
 * - Treated as free functions with name mangling
 * - Class name prefix applied for scoping
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper);
 * StaticMethodHandler::registerWith(dispatcher);
 *
 * CXXMethodDecl* staticMethod = ...;  // static method
 * dispatcher.dispatch(cppCtx, cCtx, staticMethod);
 * // → Creates C FunctionDecl: ClassName__methodName
 * @endcode
 */
class StaticMethodHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for static CXXMethodDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Compute mangled name for static method
     * @param method Static method declaration
     * @param classDecl Parent class declaration
     * @return Mangled name with class prefix (e.g., "Counter__getValue")
     *
     * Algorithm:
     * 1. Get class name from parent CXXRecordDecl
     * 2. Get method name from CXXMethodDecl
     * 3. Check if class is in namespace:
     *    - Walk parent DeclContexts to find NamespaceDecl
     *    - Compute namespace path (A::B → A__B)
     *    - Prefix class name with namespace path
     * 4. Combine class name and method name with __ separator
     * 5. Return mangled name
     *
     * Examples:
     * - Simple: Counter::getValue() → "Counter__getValue"
     * - Namespace: game::Entity::getMax() → "game__Entity__getMax"
     * - Nested namespace: ns1::ns2::Math::add() → "ns1__ns2__Math__add"
     *
     * Critical: Uses __ separator (NOT _) for all C++ scope resolution
     * - C++ :: becomes C __
     * - Ensures consistency with other handlers
     *
     * Made public for testing
     */
    static std::string getMangledName(
        const clang::CXXMethodDecl* method,
        const clang::CXXRecordDecl* classDecl
    );

private:
    /**
     * @brief Predicate: Check if declaration is static CXXMethodDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is static CXXMethodDecl AND NOT constructor/destructor
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     * 3. Accept only CXXMethod kind (exclude plain Function)
     * 4. Cast to CXXMethodDecl and check isStatic()
     * 5. Exclude constructors and destructors (separate handlers)
     *
     * Critical: EXACT type matching
     * - Use getKind() == Decl::CXXMethod (NOT isa<>)
     * - Ensures we only handle static methods
     * - Instance methods handled by MethodHandler
     * - Constructors/destructors handled by dedicated handlers
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ static method to C function
     * @param disp Dispatcher for accessing PathMapper and delegating translation
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D Static CXXMethodDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is static CXXMethodDecl
     * 2. Cast D to CXXMethodDecl
     * 3. Get parent class (CXXRecordDecl)
     * 4. Compute mangled name using getMangledName():
     *    - Apply class name prefix
     *    - Apply namespace prefix if applicable
     *    - Use __ separator for all scope resolution
     * 5. Translate return type via TypeHandler:
     *    - Dispatch return type to TypeHandler
     *    - Retrieve translated type from TypeMapper
     *    - References → pointers conversion handled by TypeHandler
     * 6. Translate parameters via ParameterHandler:
     *    - Dispatch each parameter to ParameterHandler
     *    - Retrieve created C parameters from DeclMapper
     *    - NO "this" parameter (static methods are free functions)
     * 7. Translate function body (if exists) via CompoundStmtHandler:
     *    - Dispatch body statement to CompoundStmtHandler
     *    - Retrieve created C body from StmtMapper
     * 8. Create C FunctionDecl with:
     *    - Mangled name (class prefix applied)
     *    - Translated return type
     *    - Translated parameters (no "this")
     *    - Translated body (or nullptr if no body)
     * 9. Get target path and C TranslationUnit
     * 10. Add C function to C TranslationUnit
     * 11. Register node location in PathMapper
     * 12. Store declaration mapping in DeclMapper
     *
     * Delegation Strategy (Chain of Responsibility):
     * - TypeHandler: Handles all type translation (references → pointers)
     * - ParameterHandler: Handles each parameter translation
     * - CompoundStmtHandler: Handles function body translation
     * - This handler: Orchestrates and applies name mangling
     *
     * Name Mangling:
     * - C++ Counter::getValue() → C Counter__getValue()
     * - C++ game::Entity::getMax() → C game__Entity__getMax()
     * - C++ ns1::ns2::Math::add() → C ns1__ns2__Math__add()
     *
     * @pre D != nullptr && D->getKind() == Decl::CXXMethod && isStatic() (asserted)
     */
    static void handleStaticMethod(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Translate method parameters by dispatching to ParameterHandler
     * @param method Static method declaration
     * @param disp Dispatcher for parameter translation
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @return Vector of C ParmVarDecl (created by ParameterHandler)
     *
     * Follows Chain of Responsibility pattern: Dispatches each parameter
     * to ParameterHandler, then retrieves created C parameters via DeclMapper.
     *
     * Critical: NO "this" parameter for static methods
     * - Static methods are class-scoped free functions
     * - Only translate actual method parameters
     */
    static std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::CXXMethodDecl* method,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
