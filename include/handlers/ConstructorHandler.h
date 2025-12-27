/**
 * @file ConstructorHandler.h
 * @brief Handler for translating C++ constructors to C init functions
 *
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
 *
 * Out of Scope (Future):
 * - Delegating constructors (calling other constructors)
 * - Base class constructor calls (inheritance - Phase 45)
 * - Complex member initializer lists with function calls
 */

#pragma once

#include "handlers/ASTHandler.h"
#include "clang/AST/DeclCXX.h"

namespace cpptoc {

/**
 * @class ConstructorHandler
 * @brief Translates C++ constructors to C init functions
 *
 * Example Translation:
 * C++: Counter() : count(0) {}
 * C:   void Counter_init(struct Counter* this) { this->count = 0; }
 *
 * C++: Counter(int initial) : count(initial) {}
 * C:   void Counter_init_int(struct Counter* this, int initial) {
 *          this->count = initial;
 *      }
 */
class ConstructorHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes constructor declarations
     */
    bool canHandle(const clang::Decl* D) const override;

    /**
     * @brief Translate C++ constructor to C init function
     * @param D C++ CXXConstructorDecl
     * @param ctx Handler context
     * @return C FunctionDecl (init function)
     *
     * Translation process:
     * 1. Extract class name (e.g., "Counter")
     * 2. Generate function name: ClassName_init or ClassName_init_types
     * 3. Add first parameter: struct ClassName* this
     * 4. Add constructor parameters after this parameter
     * 5. Translate member initializer list to assignments
     * 6. Translate constructor body
     * 7. Create C FunctionDecl with void return type
     */
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;

private:
    /**
     * @brief Generate mangled function name for constructor
     * @param className Name of the class
     * @param ctor Constructor declaration
     * @return Mangled function name (e.g., "Counter_init" or "Counter_init_int_int")
     *
     * Naming convention:
     * - No parameters: ClassName_init
     * - With parameters: ClassName_init_type1_type2_...
     *   Example: Counter_init_int for Counter(int)
     */
    std::string generateConstructorName(
        const std::string& className,
        const clang::CXXConstructorDecl* ctor
    );

    /**
     * @brief Translate constructor parameters
     * @param ctor C++ constructor declaration
     * @param ctx Handler context
     * @return Vector of C parameters (not including 'this' parameter)
     */
    std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::CXXConstructorDecl* ctor,
        HandlerContext& ctx
    );

    /**
     * @brief Create 'this' parameter for init function
     * @param recordType Type of the class/struct
     * @param ctx Handler context
     * @return ParmVarDecl for 'this' parameter (struct ClassName* this)
     */
    clang::ParmVarDecl* createThisParameter(
        clang::QualType recordType,
        HandlerContext& ctx
    );

    /**
     * @brief Translate type to C type (handle references, etc.)
     * @param cppType C++ type
     * @param ctx Handler context
     * @return C type (with reference types converted to pointers)
     */
    clang::QualType translateType(
        clang::QualType cppType,
        HandlerContext& ctx
    );

    /**
     * @brief Get simple type name for mangling
     * @param type QualType to get name from
     * @return Simple type name (e.g., "int", "float", "Counter")
     *
     * Used for constructor name mangling.
     */
    std::string getSimpleTypeName(clang::QualType type) const;

    /**
     * @brief Inject lpVtbl initialization as first statements in constructor body
     * @param parentClass C++ class (CXXRecordDecl)
     * @param thisParam C this parameter (struct ClassName* this)
     * @param ctx Handler context
     * @return Vector of statements for all lpVtbl initializations
     *
     * Only injects if class is polymorphic (has virtual methods).
     * Pattern (COM/DCOM ABI):
     *   Single inheritance:
     *     this->lpVtbl = &ClassName_vtable_instance;
     *   Multiple inheritance:
     *     this->lpVtbl = &ClassName_Base1_vtable_instance;
     *     this->lpVtbl2 = &ClassName_Base2_vtable_instance;
     *     this->lpVtbl3 = &ClassName_Base3_vtable_instance;
     *
     * These MUST be the first statements in the constructor body.
     */
    std::vector<clang::Stmt*> injectLpVtblInit(
        const clang::CXXRecordDecl* parentClass,
        clang::ParmVarDecl* thisParam,
        HandlerContext& ctx
    );

    /**
     * @brief Generate base constructor calls for derived class constructor
     * @param ctor C++ constructor declaration
     * @param thisParam C this parameter
     * @param ctx Handler context
     * @return Vector of base constructor call statements
     *
     * Pattern (Phase 46 Group 3 Task 8):
     *   Base1_init((struct Base1*)this);
     *   Base2_init((struct Base2*)((char*)this + offset));
     *
     * For single inheritance or primary base: direct pointer cast
     * For non-primary bases: pointer adjustment using offset
     */
    std::vector<clang::Stmt*> generateBaseConstructorCalls(
        const clang::CXXConstructorDecl* ctor,
        clang::ParmVarDecl* thisParam,
        HandlerContext& ctx
    );

    /**
     * @brief Create call to base constructor
     * @param baseClass Base class to initialize
     * @param thisParam C this parameter
     * @param offset Offset of base in derived class (0 for primary base)
     * @param ctx Handler context
     * @return CallExpr for base constructor
     */
    clang::CallExpr* createBaseConstructorCall(
        const clang::CXXRecordDecl* baseClass,
        clang::ParmVarDecl* thisParam,
        unsigned offset,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
