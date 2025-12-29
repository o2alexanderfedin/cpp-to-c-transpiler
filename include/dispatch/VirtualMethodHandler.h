/**
 * @file VirtualMethodHandler.h
 * @brief Handler for processing virtual CXXMethodDecl nodes with COM-style vtables
 *
 * Registers with CppToCVisitorDispatcher to handle C++ virtual method declarations.
 * Generates COM-style vtables with strongly typed function pointers, static declarations
 * for compile-time type safety, and __vptr fields in polymorphic structs.
 *
 * Phase 1 Scope: Virtual method translation with vtable generation
 * - Virtual method detection (isVirtual() == true, NOT static/ctor/dtor)
 * - COM-style static declarations (compile-time type safety)
 * - Vtable struct with strongly typed function pointers
 * - Vtable instance initialization
 * - __vptr field in polymorphic structs
 * - Class/namespace prefixing with __ separator
 * - Function bodies translated via CompoundStmtHandler
 *
 * Future Phases:
 * - Virtual method overloading resolution
 * - Template virtual methods
 * - Virtual base offset tables
 * - RTTI type_info integration
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include <vector>
#include <string>

namespace cpptoc {

/**
 * @class VirtualMethodHandler
 * @brief Processes virtual CXXMethodDecl and creates C functions with vtable support
 *
 * Responsibilities:
 * - Match virtual CXXMethodDecl nodes (predicate) - EXCLUDING constructors/destructors/static
 * - Translate virtual method signature (name, return type, parameters)
 * - Generate COM-style static declarations for compile-time type safety
 * - Generate vtable struct with strongly typed function pointers
 * - Generate vtable instance with method initializers
 * - Add __vptr field to polymorphic structs (coordinates with RecordHandler)
 * - Apply class name prefix with __ separator (Class::method → Class__method)
 * - Apply namespace prefix if class is in namespace (NS::Class::method → NS__Class__method)
 * - Convert C++ references to C pointers in signature
 * - Create C FunctionDecl with translated signature and body
 * - Add translated function to appropriate C TranslationUnit
 *
 * COM-Style Vtable Pattern:
 * ```c
 * // Static declarations (compile-time type safety)
 * static void Shape__dtor(struct Shape *this);
 * static int Shape__getArea(struct Shape *this);
 *
 * // Vtable structure (strongly typed function pointers)
 * struct Shape__vtable {
 *     const struct __class_type_info *type_info;  // RTTI
 *     void (*destructor)(struct Shape *this);
 *     int (*getArea)(struct Shape *this);
 * };
 *
 * // Vtable instance initialization
 * static struct Shape__vtable Shape__vtable_instance = {
 *     .type_info = &Shape__type_info,
 *     .destructor = Shape__dtor,
 *     .getArea = Shape__getArea
 * };
 *
 * // Struct with vptr
 * struct Shape {
 *     const struct Shape__vtable *__vptr;  // Virtual pointer
 * };
 * ```
 *
 * Translation Example:
 * C++:  class Shape {
 *       public:
 *           virtual int getArea() { return 0; }
 *       };
 *
 * C:    static int Shape__getArea(struct Shape* this);
 *       int Shape__getArea(struct Shape* this) { return 0; }
 *
 * Namespace Example:
 * C++:  namespace game {
 *           class Entity {
 *           public:
 *               virtual void update() {}
 *           };
 *       }
 *
 * C:    static void game__Entity__update(struct game__Entity* this);
 *       void game__Entity__update(struct game__Entity* this) {}
 *
 * Key Differences from InstanceMethodHandler:
 * - Virtual methods stored in vtable (instance methods are direct calls)
 * - Generates static declarations for compile-time safety
 * - Generates vtable struct and instance
 * - Adds __vptr field to struct (coordinates with RecordHandler)
 * - Same name mangling pattern (__ separator)
 *
 * Key Differences from StaticMethodHandler:
 * - Has "this" parameter (static methods have NO "this")
 * - Generates vtable infrastructure (static methods don't)
 * - Same name mangling pattern (__ separator)
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper);
 * VirtualMethodHandler::registerWith(dispatcher);
 *
 * CXXMethodDecl* virtualMethod = ...;  // virtual method
 * dispatcher.dispatch(cppCtx, cCtx, virtualMethod);
 * // → Creates C FunctionDecl: ClassName__methodName
 * // → Generates static declaration
 * // → Adds to vtable struct
 * // → Initializes vtable instance
 * @endcode
 */
class VirtualMethodHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for virtual CXXMethodDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Compute mangled name for virtual method
     * @param method Virtual method declaration
     * @param classDecl Parent class declaration
     * @return Mangled name with class prefix (e.g., "Shape__getArea")
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
     * - Simple: Shape::getArea() → "Shape__getArea"
     * - Namespace: game::Entity::update() → "game__Entity__update"
     * - Nested namespace: ns1::ns2::Math::add() → "ns1__ns2__Math__add"
     *
     * Critical: Uses __ separator (NOT _) for all C++ scope resolution
     * - C++ :: becomes C __
     * - Ensures consistency with StaticMethodHandler and InstanceMethodHandler
     *
     * Note: SAME implementation as StaticMethodHandler::getMangledName()
     * and InstanceMethodHandler::getMangledName()
     * - All method types use identical name mangling
     * - Only difference is vtable generation for virtual methods
     *
     * Made public for testing
     */
    static std::string getMangledName(
        const clang::CXXMethodDecl* method,
        const clang::CXXRecordDecl* classDecl
    );

    /**
     * @brief Create "this" parameter for virtual method
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
     * - Simple class: Shape → "struct Shape* this"
     * - Namespace class: game::Entity → "struct game__Entity* this"
     * - Nested namespace: ns1::ns2::Math → "struct ns1__ns2__Math* this"
     *
     * Critical: "this" parameter type MUST match struct name in C output
     * - If class is Shape, struct is Shape
     * - If class is game::Entity, struct is game__Entity
     * - Namespace prefix applied consistently
     *
     * Note: This parameter is ALWAYS FIRST in parameter list
     * - Before all method parameters
     * - Essential for accessing instance members in C
     *
     * Note: SAME implementation as InstanceMethodHandler::createThisParameter()
     * - Both virtual and instance methods use same "this" parameter
     * - Only difference is vtable generation for virtual methods
     *
     * Made public for testing
     */
    static clang::ParmVarDecl* createThisParameter(
        const clang::CXXRecordDecl* classDecl,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Generate COM-style static declaration for virtual method
     * @param method Virtual method declaration
     * @param classDecl Parent class declaration
     * @param cASTContext Target C ASTContext
     * @return Static declaration string (e.g., "static int Shape__getArea(struct Shape *this);")
     *
     * Algorithm:
     * 1. Get mangled name using getMangledName()
     * 2. Get return type (translate via TypeHandler)
     * 3. Build parameter list (this + method params)
     * 4. Format as: "static ReturnType MangledName(params);"
     *
     * Examples:
     * - Simple: "static int Shape__getArea(struct Shape *this);"
     * - With params: "static int Math__add(struct Math *this, int a, int b);"
     * - Namespace: "static void game__Entity__update(struct game__Entity *this);"
     *
     * Critical: Provides compile-time type safety
     * - If method signature changes, compiler catches mismatch
     * - Prevents runtime crashes from wrong vtable assignments
     *
     * Placement: Generated BEFORE vtable struct definitions
     *
     * Made public for testing
     */
    static std::string generateStaticDeclaration(
        const clang::CXXMethodDecl* method,
        const clang::CXXRecordDecl* classDecl,
        clang::ASTContext& cASTContext
    );

private:
    /**
     * @brief Predicate: Check if declaration is virtual CXXMethodDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is virtual CXXMethodDecl AND NOT constructor/destructor/static
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     * 3. Accept only CXXMethod kind (exclude plain Function)
     * 4. Cast to CXXMethodDecl and check:
     *    - NOT constructor (exclude CXXConstructorDecl)
     *    - NOT destructor (exclude CXXDestructorDecl)
     *    - NOT static (exclude static methods)
     *    - IS virtual (isVirtual() == true)
     * 5. Return true only for virtual instance methods
     *
     * Critical: EXACT type matching and comprehensive filters
     * - Use getKind() == Decl::CXXMethod (NOT isa<>)
     * - Exclude ctors/dtors (have dedicated handlers)
     * - Exclude static methods (handled by StaticMethodHandler)
     * - Exclude non-virtual methods (handled by InstanceMethodHandler)
     * - Accept ONLY virtual instance methods
     *
     * Filtering Logic:
     * - CXXMethodDecl: YES (base type)
     * - CXXConstructorDecl: NO (excluded explicitly)
     * - CXXDestructorDecl: NO (excluded explicitly, even if virtual)
     * - Static CXXMethodDecl: NO (isStatic() check)
     * - Non-virtual CXXMethodDecl: NO (isVirtual() check)
     * - Virtual instance method: YES (passes all filters)
     *
     * Complementary Filtering:
     * - StaticMethodHandler: isStatic() == true (NO this, NO vtable)
     * - InstanceMethodHandler: !isStatic() && !isVirtual() (WITH this, NO vtable)
     * - VirtualMethodHandler: !isStatic() && isVirtual() (WITH this, WITH vtable)
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ virtual method to C function with vtable support
     * @param disp Dispatcher for accessing PathMapper and delegating translation
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D Virtual CXXMethodDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is virtual CXXMethodDecl
     * 2. Cast D to CXXMethodDecl
     * 3. Get parent class (CXXRecordDecl)
     * 4. Compute mangled name using getMangledName():
     *    - Apply class name prefix
     *    - Apply namespace prefix if applicable
     *    - Use __ separator for all scope resolution
     * 5. Generate COM-style static declaration:
     *    - Call generateStaticDeclaration()
     *    - Store for later output (before vtable struct)
     * 6. Translate return type via TypeHandler:
     *    - Dispatch return type to TypeHandler
     *    - Retrieve translated type from TypeMapper
     *    - References → pointers conversion handled by TypeHandler
     * 7. Create "this" parameter using createThisParameter():
     *    - Type: struct ClassName* (with namespace prefix)
     *    - Name: "this"
     *    - Position: FIRST parameter
     * 8. Translate method parameters via ParameterHandler:
     *    - Dispatch each parameter to ParameterHandler
     *    - Retrieve created C parameters from DeclMapper
     * 9. Combine parameters: [this] + method_parameters
     *    - "this" is FIRST
     *    - Followed by translated method parameters
     * 10. Translate function body (if exists) via CompoundStmtHandler:
     *     - Dispatch body statement to CompoundStmtHandler
     *     - Retrieve created C body from StmtMapper
     *     - Pure virtual methods have no body
     * 11. Create C FunctionDecl with:
     *     - Mangled name (class prefix applied)
     *     - Translated return type
     *     - Combined parameters (this + method params)
     *     - Translated body (or nullptr if pure virtual)
     * 12. Register in vtable tracking (for vtable struct generation):
     *     - Add method to class vtable method list
     *     - Track method signature for vtable struct
     *     - Track method pointer for vtable instance
     * 13. Coordinate with RecordHandler for __vptr field:
     *     - Mark class as polymorphic
     *     - RecordHandler will add __vptr field
     * 14. Get target path and C TranslationUnit
     * 15. Add C function to C TranslationUnit
     * 16. Register node location in PathMapper
     * 17. Store declaration mapping in DeclMapper
     *
     * Delegation Strategy (Chain of Responsibility):
     * - TypeHandler: Handles all type translation (references → pointers)
     * - ParameterHandler: Handles each parameter translation
     * - CompoundStmtHandler: Handles function body translation
     * - RecordHandler: Adds __vptr field to polymorphic structs
     * - This handler: Orchestrates and generates vtable infrastructure
     *
     * Name Mangling:
     * - C++ Shape::getArea() → C Shape__getArea(struct Shape* this)
     * - C++ game::Entity::update() → C game__Entity__update(struct game__Entity* this)
     * - C++ ns1::ns2::Math::add() → C ns1__ns2__Math__add(struct ns1__ns2__Math* this, ...)
     *
     * Vtable Generation:
     * - Static declaration: "static int Shape__getArea(struct Shape *this);"
     * - Vtable struct field: "int (*getArea)(struct Shape *this);"
     * - Vtable instance init: ".getArea = Shape__getArea"
     * - Struct vptr field: "const struct Shape__vtable *__vptr;"
     *
     * @pre D != nullptr && D->getKind() == Decl::CXXMethod && !isStatic() && isVirtual() (asserted)
     */
    static void handleVirtualMethod(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Translate method parameters by dispatching to ParameterHandler
     * @param method Virtual method declaration
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

    /**
     * @brief Get namespace prefix for class (if in namespace)
     * @param classDecl Class declaration
     * @return Namespace prefix with __ separators (empty if no namespace)
     *
     * Algorithm:
     * 1. Walk parent DeclContexts from class
     * 2. Collect NamespaceDecl names
     * 3. Build prefix: ns1__ns2__ (with trailing __)
     * 4. Return empty string if no namespaces
     *
     * Examples:
     * - No namespace: "" (empty)
     * - Single namespace: "game__"
     * - Nested namespace: "ns1__ns2__"
     *
     * Critical: Always includes trailing __ if namespace exists
     * - Allows simple concatenation: prefix + className
     * - Consistent with other handlers
     */
    static std::string getNamespacePrefix(const clang::CXXRecordDecl* classDecl);

public:
    /**
     * @brief Generate vtable struct definition for a class
     * @param classDecl C++ class declaration
     * @param virtualMethods List of virtual methods in vtable order
     * @param cASTContext C AST context
     * @return Vtable struct definition string
     *
     * Algorithm:
     * 1. Get class name with namespace prefix
     * 2. Generate struct ClassName__vtable {
     * 3. Add RTTI type_info pointer as first field
     * 4. For each virtual method:
     *    - Generate strongly typed function pointer field
     *    - Special case for destructor: void (*destructor)(struct ClassName *this)
     *    - Regular method: ReturnType (*methodName)(struct ClassName *this, params...)
     * 5. Close struct definition
     *
     * Example Output:
     * struct Shape__vtable {
     *     const struct __class_type_info *type_info;
     *     void (*destructor)(struct Shape *this);
     *     int (*getArea)(struct Shape *this);
     *     void (*draw)(struct Shape *this);
     * };
     *
     * Critical: Strongly typed function pointers (NOT generic void*)
     * - Each class gets its own vtable struct type
     * - Function signatures match exact method signatures
     * - COM/DCOM pattern for type safety
     *
     * Made public for testing
     */
    static std::string generateVtableStruct(
        const clang::CXXRecordDecl* classDecl,
        const std::vector<const clang::CXXMethodDecl*>& virtualMethods,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Generate vtable instance initialization
     * @param classDecl C++ class declaration
     * @param virtualMethods List of virtual methods in vtable order
     * @param cASTContext C AST context
     * @return Vtable instance initialization string
     *
     * Algorithm:
     * 1. Get class name with namespace prefix
     * 2. Generate static struct ClassName__vtable ClassName__vtable_instance = {
     * 3. Initialize .type_info = &ClassName__type_info
     * 4. For each virtual method:
     *    - Initialize .destructor = ClassName__dtor (for destructor)
     *    - Initialize .methodName = ClassName__methodName (for methods)
     * 5. Close initializer
     *
     * Example Output:
     * static struct Shape__vtable Shape__vtable_instance = {
     *     .type_info = &Shape__type_info,
     *     .destructor = Shape__dtor,
     *     .getArea = Shape__getArea,
     *     .draw = Shape__draw
     * };
     *
     * Critical: Uses designated initializers (C99)
     * - Type-safe assignment of function pointers
     * - Compiler verifies signature matches vtable struct
     *
     * Made public for testing
     */
    static std::string generateVtableInstance(
        const clang::CXXRecordDecl* classDecl,
        const std::vector<const clang::CXXMethodDecl*>& virtualMethods,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Get mangled vtable struct name
     * @param classDecl C++ class declaration
     * @return Vtable struct name (e.g., "Shape__vtable")
     *
     * Algorithm:
     * 1. Get class name
     * 2. Apply namespace prefix if in namespace
     * 3. Append "__vtable"
     *
     * Examples:
     * - Simple: Shape → "Shape__vtable"
     * - Namespace: game::Entity → "game__Entity__vtable"
     *
     * Made public for testing
     */
    static std::string getVtableStructName(const clang::CXXRecordDecl* classDecl);

    /**
     * @brief Get mangled vtable instance name
     * @param classDecl C++ class declaration
     * @return Vtable instance name (e.g., "Shape__vtable_instance")
     *
     * Algorithm:
     * 1. Get class name
     * 2. Apply namespace prefix if in namespace
     * 3. Append "__vtable_instance"
     *
     * Examples:
     * - Simple: Shape → "Shape__vtable_instance"
     * - Namespace: game::Entity → "game__Entity__vtable_instance"
     *
     * Made public for testing
     */
    static std::string getVtableInstanceName(const clang::CXXRecordDecl* classDecl);

private:
    /**
     * @brief Generate function pointer type for vtable field
     * @param method Virtual method declaration
     * @param className Fully qualified class name (with namespace prefix)
     * @param cASTContext C AST context
     * @return Function pointer type string
     *
     * Algorithm:
     * 1. Get return type (translate via type helpers)
     * 2. Build parameter list: struct ClassName *this + method params
     * 3. Format as: ReturnType (*)(struct ClassName *this, params...)
     *
     * Example Output:
     * - int (*)(struct Shape *this)
     * - void (*)(struct Shape *this, int x, int y)
     *
     * Critical: Strongly typed signature
     * - NOT generic void* function pointers
     * - Exact parameter types preserved
     *
     * Helper for generateVtableStruct()
     */
    static std::string generateFunctionPointerType(
        const clang::CXXMethodDecl* method,
        const std::string& className,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
