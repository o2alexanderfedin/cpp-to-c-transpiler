/**
 * @file InstanceMethodHandler.h
 * @brief Handler for processing non-static, non-virtual instance methods
 *
 * Registers with CppToCVisitorDispatcher to handle C++ instance method declarations.
 * Translates instance methods to C free functions with explicit "this" parameter and
 * class/namespace prefixing.
 *
 * Phase 1 Scope: Instance method signature translation
 * - Instance method name with class/namespace prefix (Class__method)
 * - Return type and parameter translation
 * - Explicit "this" parameter as FIRST parameter (struct ClassName* this)
 * - Function bodies translated via CompoundStmtHandler
 * - EXCLUDES: static methods, virtual methods, constructors, destructors
 *
 * Future Phases:
 * - Method overloading resolution
 * - Template instance methods
 * - Const method handling (const qualifier on "this")
 * - Member function pointers
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
 * @class InstanceMethodHandler
 * @brief Processes non-static, non-virtual instance methods to C functions with "this"
 *
 * Responsibilities:
 * - Match non-static, non-virtual CXXMethodDecl nodes (predicate)
 * - EXCLUDE constructors, destructors, static methods, virtual methods
 * - Translate instance method signature (name, return type, parameters)
 * - Create explicit "this" parameter as FIRST parameter
 * - Apply class name prefix with __ separator (Class::method → Class__method)
 * - Apply namespace prefix if class is in namespace (NS::Class::method → NS__Class__method)
 * - Convert C++ references to C pointers in signature
 * - Create C FunctionDecl with "this" parameter and translated signature
 * - Add translated function to appropriate C TranslationUnit
 *
 * Translation Example:
 * C++:  class Counter {
 *       public:
 *           void increment() { value++; }
 *       private:
 *           int value;
 *       };
 *
 * C:    void Counter__increment(struct Counter* this);
 *       void Counter__increment(struct Counter* this) { this->value++; }
 *
 * Namespace Example:
 * C++:  namespace game {
 *           class Entity {
 *           public:
 *               void update() { x += vx; }
 *           };
 *       }
 *
 * C:    void game__Entity__update(struct game__Entity* this);
 *       void game__Entity__update(struct game__Entity* this) { this->x += this->vx; }
 *
 * Parameters Example:
 * C++:  class Math {
 *       public:
 *           int add(int a, int b) { return a + b + offset; }
 *       private:
 *           int offset;
 *       };
 *
 * C:    int Math__add(struct Math* this, int a, int b);
 *       int Math__add(struct Math* this, int a, int b) { return a + b + this->offset; }
 *
 * Key Differences from StaticMethodHandler:
 * - Has "this" parameter as FIRST parameter (static methods have NO "this")
 * - "this" type is pointer to struct with class name
 * - Same name mangling pattern as static methods
 * - Both use __ separator for all C++ scope resolution
 *
 * Key Differences from Constructors/Destructors:
 * - Regular methods have return types (ctors/dtors don't)
 * - Regular methods called on existing instance
 * - Constructors allocate/initialize, destructors cleanup
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper);
 * InstanceMethodHandler::registerWith(dispatcher);
 *
 * CXXMethodDecl* instanceMethod = ...;  // non-static, non-virtual method
 * dispatcher.dispatch(cppCtx, cCtx, instanceMethod);
 * // → Creates C FunctionDecl: ClassName__methodName(struct ClassName* this, ...)
 * @endcode
 */
class InstanceMethodHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for instance CXXMethodDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Compute mangled name for instance method
     * @param method Instance method declaration
     * @param classDecl Parent class declaration
     * @return Mangled name with class prefix (e.g., "Counter__increment")
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
     * - Simple: Counter::increment() → "Counter__increment"
     * - Namespace: game::Entity::update() → "game__Entity__update"
     * - Nested namespace: ns1::ns2::Math::add() → "ns1__ns2__Math__add"
     *
     * Critical: Uses __ separator (NOT _) for all C++ scope resolution
     * - C++ :: becomes C __
     * - Ensures consistency with StaticMethodHandler and other handlers
     *
     * Note: SAME implementation as StaticMethodHandler::getMangledName()
     * - Both static and instance methods use identical name mangling
     * - Only difference is "this" parameter presence
     *
     * Made public for testing
     */
    static std::string getMangledName(
        const clang::CXXMethodDecl* method,
        const clang::CXXRecordDecl* classDecl
    );

    /**
     * @brief Create "this" parameter for instance method
     * @param classDecl Parent class declaration
     * @param cASTContext Target C ASTContext (where to create parameter)
     * @return ParmVarDecl representing "struct ClassName* this"
     *
     * Algorithm:
     * 1. Get class name from CXXRecordDecl
     * 2. Check if class is in namespace:
     *    - Walk parent DeclContexts to find NamespaceDecl
     *    - Compute namespace path (A::B → A__B)
     *    - Prefix class name with namespace path
     * 3. Create struct type with prefixed class name
     * 4. Create pointer type to struct
     * 5. Create ParmVarDecl with:
     *    - Name: "this"
     *    - Type: struct ClassName* (pointer to struct)
     *    - Storage class: SC_None
     *
     * Examples:
     * - Simple class: Counter → "struct Counter* this"
     * - Namespace class: game::Entity → "struct game__Entity* this"
     * - Nested namespace: ns1::ns2::Math → "struct ns1__ns2__Math* this"
     *
     * Critical: "this" parameter type MUST match struct name in C output
     * - If class is Counter, struct is Counter
     * - If class is game::Entity, struct is game__Entity
     * - Namespace prefix applied consistently
     *
     * Note: This parameter is ALWAYS FIRST in parameter list
     * - Before all method parameters
     * - Essential for accessing instance members in C
     *
     * Made public for testing
     */
    static clang::ParmVarDecl* createThisParameter(
        const clang::CXXRecordDecl* classDecl,
        clang::ASTContext& cASTContext
    );

private:
    /**
     * @brief Predicate: Check if declaration is non-static, non-virtual instance method
     * @param D Declaration to check (must not be null)
     * @return true if D is instance CXXMethodDecl AND NOT ctor/dtor/static/virtual
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     * 3. Accept only CXXMethod kind (exclude plain Function)
     * 4. Cast to CXXMethodDecl and check:
     *    - NOT constructor (exclude CXXConstructorDecl)
     *    - NOT destructor (exclude CXXDestructorDecl)
     *    - NOT static (exclude static methods)
     *    - NOT virtual (exclude virtual methods)
     * 5. Return true only for regular instance methods
     *
     * Critical: EXACT type matching and comprehensive exclusions
     * - Use getKind() == Decl::CXXMethod (NOT isa<>)
     * - Exclude ctors/dtors (have dedicated handlers)
     * - Exclude static methods (handled by StaticMethodHandler)
     * - Exclude virtual methods (will be handled by VirtualMethodHandler)
     * - Accept ONLY non-static, non-virtual instance methods
     *
     * Filtering Logic:
     * - CXXMethodDecl: YES (base type)
     * - CXXConstructorDecl: NO (excluded explicitly)
     * - CXXDestructorDecl: NO (excluded explicitly)
     * - Static CXXMethodDecl: NO (isStatic() check)
     * - Virtual CXXMethodDecl: NO (isVirtual() check)
     * - Regular instance method: YES (passes all filters)
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ instance method to C function with "this"
     * @param disp Dispatcher for accessing PathMapper and delegating translation
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D Instance CXXMethodDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is instance CXXMethodDecl
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
     * 6. Create "this" parameter using createThisParameter():
     *    - Type: struct ClassName* (with namespace prefix)
     *    - Name: "this"
     *    - Position: FIRST parameter
     * 7. Translate method parameters via ParameterHandler:
     *    - Dispatch each parameter to ParameterHandler
     *    - Retrieve created C parameters from DeclMapper
     * 8. Combine parameters: [this] + method_parameters
     *    - "this" is FIRST
     *    - Followed by translated method parameters
     * 9. Translate function body (if exists) via CompoundStmtHandler:
     *    - Dispatch body statement to CompoundStmtHandler
     *    - Retrieve created C body from StmtMapper
     * 10. Create C FunctionDecl with:
     *     - Mangled name (class prefix applied)
     *     - Translated return type
     *     - Combined parameters (this + method params)
     *     - Translated body (or nullptr if no body)
     * 11. Get target path and C TranslationUnit
     * 12. Add C function to C TranslationUnit
     * 13. Register node location in PathMapper
     * 14. Store declaration mapping in DeclMapper
     *
     * Delegation Strategy (Chain of Responsibility):
     * - TypeHandler: Handles all type translation (references → pointers)
     * - ParameterHandler: Handles each parameter translation
     * - CompoundStmtHandler: Handles function body translation
     * - This handler: Orchestrates and applies name mangling + "this" creation
     *
     * Name Mangling (SAME as StaticMethodHandler):
     * - C++ Counter::increment() → C Counter__increment(struct Counter* this)
     * - C++ game::Entity::update() → C game__Entity__update(struct game__Entity* this)
     * - C++ ns1::ns2::Math::add(int,int) → C ns1__ns2__Math__add(struct ns1__ns2__Math* this, int, int)
     *
     * This Parameter:
     * - Always FIRST parameter
     * - Type: struct ClassName* (with namespace prefix)
     * - Name: "this" (C keyword, but allowed in parameter position)
     * - Enables access to instance members in C function body
     *
     * @pre D != nullptr && D->getKind() == Decl::CXXMethod && !isStatic() && !isVirtual() (asserted)
     */
    static void handleInstanceMethod(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Translate method parameters by dispatching to ParameterHandler
     * @param method Instance method declaration
     * @param disp Dispatcher for parameter translation
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @return Vector of C ParmVarDecl (created by ParameterHandler)
     *
     * Follows Chain of Responsibility pattern: Dispatches each parameter
     * to ParameterHandler, then retrieves created C parameters via DeclMapper.
     *
     * Critical: This returns ONLY the method's parameters
     * - Does NOT include "this" parameter
     * - "this" is created separately by createThisParameter()
     * - "this" is prepended to this list by caller
     *
     * Parameter Translation:
     * - int a → int a (pass-through)
     * - int& b → int* b (reference to pointer)
     * - const int& c → const int* c (const reference to const pointer)
     */
    static std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::CXXMethodDecl* method,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
