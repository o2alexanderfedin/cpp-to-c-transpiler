/**
 * @file ConstructorHandler.h
 * @brief Handler for translating C++ constructors to C init functions
 *
 * Registers with CppToCVisitorDispatcher to handle C++ constructor declarations.
 * Translates C++ constructors to C initialization functions with explicit
 * `this` parameter. Handles constructor bodies, parameters, and member
 * initializer lists.
 *
 * Scope (Phase 44):
 * - Default constructors (no parameters)
 * - Parameterized constructors
 * - Member initialization in constructor body
 * - Simple member initializer lists (: field(value))
 * - Constructor overloading (using name mangling)
 * - Virtual table (lpVtbl) initialization for polymorphic classes
 * - Base class constructor calls for derived classes
 *
 * Out of Scope (Future):
 * - Delegating constructors (calling other constructors)
 * - Complex member initializer lists with function calls
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/DeclCXX.h"

namespace cpptoc {

/**
 * @class ConstructorHandler
 * @brief Processes CXXConstructorDecl and creates C init functions
 *
 * Example Translation:
 * C++: Counter() : count(0) {}
 * C:   void Counter_init(struct Counter* this) { this->count = 0; }
 *
 * C++: Counter(int initial) : count(initial) {}
 * C:   void Counter_init_int(struct Counter* this, int initial) {
 *          this->count = initial;
 *      }
 *
 * Virtual Method Support:
 * C++: class Base {
 *          virtual void foo();
 *          Base() {}  // Constructor
 *      };
 * C:   void Base_init(struct Base* this) {
 *          this->lpVtbl = &Base_vtable_instance;  // Injected vtable init
 *      }
 */
class ConstructorHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY CXXConstructorDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is CXXConstructorDecl
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ constructor to C init function
     * @param disp Dispatcher for accessing mappers and child handlers
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D CXXConstructorDecl to process (must not be null)
     *
     * Translation process:
     * 1. Extract class name and generate mangled function name
     * 2. Find C RecordDecl (created by RecordHandler)
     * 3. Create 'this' parameter: struct ClassName* this
     * 4. Translate constructor parameters
     * 5. Create C FunctionDecl with void return type
     * 6. Build constructor body:
     *    a. Base constructor calls (FIRST - initialize base vtables)
     *    b. lpVtbl initialization (override base vtables with derived)
     *    c. Member initializers (TODO)
     * 7. Register in DeclMapper
     * 8. Add to target C TranslationUnit
     *
     * @pre D != nullptr && isa<CXXConstructorDecl>(D) (asserted)
     */
    static void handleConstructor(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Translate constructor parameters
     * @param ctor C++ constructor declaration
     * @param disp Dispatcher for type translation
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @return Vector of C parameters (not including 'this' parameter)
     */
    static std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::CXXConstructorDecl* ctor,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create 'this' parameter for init function
     * @param recordType Type of the C struct (NOT C++ class)
     * @param cASTContext Target C ASTContext
     * @param targetLoc Valid SourceLocation for C AST node
     * @return ParmVarDecl for 'this' parameter (struct ClassName* this)
     */
    static clang::ParmVarDecl* createThisParameter(
        clang::QualType recordType,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    /**
     * @brief Translate type to C type (handle references, etc.)
     * @param cppType C++ type
     * @param cASTContext Target C ASTContext
     * @return C type (with reference types converted to pointers)
     */
    static clang::QualType translateType(
        clang::QualType cppType,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Inject lpVtbl initialization as first statements in constructor body
     * @param parentClass C++ class (CXXRecordDecl)
     * @param thisParam C this parameter (struct ClassName* this)
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param targetLoc Valid SourceLocation for C AST nodes
     * @return Vector of statements for all lpVtbl initializations
     *
     * Only injects if class is polymorphic (has virtual methods).
     * Pattern (COM/DCOM ABI):
     *   Single inheritance:
     *     this->lpVtbl = &ClassName_vtable_instance;
     *   Multiple inheritance:
     *     this->lpVtbl = &ClassName_Base1_vtable_instance;
     *     this->lpVtbl2 = &ClassName_Base2_vtable_instance;
     *
     * These MUST be placed AFTER base constructor calls.
     */
    static std::vector<clang::Stmt*> injectLpVtblInit(
        const clang::CXXRecordDecl* parentClass,
        clang::ParmVarDecl* thisParam,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    /**
     * @brief Generate base constructor calls for derived class constructor
     * @param ctor C++ constructor declaration
     * @param thisParam C this parameter
     * @param disp Dispatcher for accessing mappers
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @return Vector of base constructor call statements
     *
     * Pattern (Phase 46 Group 3 Task 8):
     *   Base1_init((struct Base1*)this);
     *   Base2_init((struct Base2*)((char*)this + offset));
     *
     * For single inheritance or primary base: direct pointer cast
     * For non-primary bases: pointer adjustment using offset
     */
    static std::vector<clang::Stmt*> generateBaseConstructorCalls(
        const clang::CXXConstructorDecl* ctor,
        clang::ParmVarDecl* thisParam,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Create call to base constructor
     * @param baseClass Base class to initialize
     * @param thisParam C this parameter
     * @param offset Offset of base in derived class (0 for primary base)
     * @param cASTContext Target C ASTContext
     * @param targetLoc Valid SourceLocation for C AST nodes
     * @return CallExpr for base constructor
     */
    static clang::CallExpr* createBaseConstructorCall(
        const clang::CXXRecordDecl* baseClass,
        clang::ParmVarDecl* thisParam,
        unsigned offset,
        clang::ASTContext& cASTContext,
        clang::SourceLocation targetLoc
    );

    /**
     * @brief Phase 3: Check if constructor needs C1/C2 splitting
     * @param ctor Constructor to check
     * @return true if class needs dual constructor variants (has virtual bases)
     *
     * Uses RecordHandler::needsDualLayout() for consistency with struct generation.
     * A constructor needs variants if its parent class requires dual layout.
     */
    static bool needsConstructorVariants(const clang::CXXConstructorDecl* ctor);

    /**
     * @brief Phase 3: Generate C1 (complete-object) constructor
     * @param ctor C++ constructor declaration
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param disp Dispatcher for accessing mappers
     *
     * C1 constructor characteristics:
     * - Function name: ClassName_ctor_C1 (or mangled variant)
     * - this parameter: ClassName* (complete-object layout)
     * - VTT parameter: const void** vtt (if needed)
     * - Initializes virtual bases (C1 responsibility)
     * - Calls non-virtual base constructors
     * - Initializes own fields
     */
    static void generateC1Constructor(
        const clang::CXXConstructorDecl* ctor,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const CppToCVisitorDispatcher& disp
    );

    /**
     * @brief Phase 3: Generate C2 (base-subobject) constructor
     * @param ctor C++ constructor declaration
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param disp Dispatcher for accessing mappers
     *
     * C2 constructor characteristics:
     * - Function name: ClassName_ctor_C2 (or mangled variant)
     * - this parameter: ClassName__base* (base-subobject layout)
     * - VTT parameter: const void** vtt (if needed)
     * - SKIPS virtual base initialization (parent's C1 handles it)
     * - Calls non-virtual base constructors
     * - Initializes own fields
     */
    static void generateC2Constructor(
        const clang::CXXConstructorDecl* ctor,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const CppToCVisitorDispatcher& disp
    );
};

} // namespace cpptoc
