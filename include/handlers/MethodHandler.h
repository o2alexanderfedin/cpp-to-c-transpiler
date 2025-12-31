/**
 * @file MethodHandler.h
 * @brief Handler for translating C++ methods to C functions with explicit this parameter
 *
 * Translates C++ member functions (methods) to regular C functions with an
 * explicit "this" parameter as the first parameter.
 *
 * Scope (Phase 44 Task 3):
 * - CXXMethodDecl translation
 * - Method name mangling (ClassName_methodName)
 * - Explicit this parameter injection (struct ClassName* this)
 * - Parameter translation
 * - Return type translation
 * - Method body translation (delegated to StatementHandler/ExpressionHandler)
 * - Static methods (no this parameter)
 * - Const methods (documented as advisory in C)
 *
 * Out of Scope (Future):
 * - Virtual methods (Phase 45 - vtable)
 * - Operator overloading (Phase 46+)
 * - Complex overload resolution (Phase 46)
 */

#pragma once

#include "handlers/ASTHandler.h"
#include "clang/AST/DeclCXX.h"
#include <string>
#include <vector>

namespace cpptoc {

/**
 * @class MethodHandler
 * @brief Translates C++ methods to C functions with explicit this parameter
 *
 * Example Translation:
 * C++: class Counter { void increment() { count++; } };
 * C:   void Counter_increment(struct Counter* this) { this->count++; }
 *
 * Static Method Translation:
 * C++: class Counter { static int getVersion() { return 1; } };
 * C:   int Counter_getVersion(void) { return 1; }  // No this parameter
 *
 * Name Mangling Strategy:
 * - Simple: ClassName::method() → ClassName_method()
 * - Overloaded methods (basic): ClassName::method(int) → ClassName_method()
 *   (Full overload mangling deferred to Phase 46)
 */
class MethodHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes C++ method declarations
     * @param D Declaration to check
     * @return true if D is a CXXMethodDecl (excluding constructors/destructors)
     */
    bool canHandle(const clang::Decl* D) const override;

    /**
     * @brief Translate C++ method to C function with this parameter
     * @param D C++ CXXMethodDecl
     * @param ctx Handler context
     * @return C FunctionDecl with this parameter (or no this for static methods)
     *
     * Translation steps:
     * 1. Extract method name and class name
     * 2. Mangle method name (ClassName_methodName)
     * 3. Translate return type
     * 4. Add this parameter (struct ClassName* this) - unless static method
     * 5. Translate parameters
     * 6. Translate method body
     * 7. Create C FunctionDecl
     * 8. Register mapping in context
     */
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;

private:
    /**
     * @brief Mangle method name with class name
     * @param className Name of the class
     * @param methodName Name of the method
     * @return Mangled name (ClassName_methodName)
     *
     * Example: mangleMethodName("Counter", "increment") → "Counter_increment"
     */
    std::string mangleMethodName(
        const std::string& className,
        const std::string& methodName
    ) const;

    /**
     * @brief Create this parameter for method
     * @param className Name of the class
     * @param ctx Handler context
     * @return ParmVarDecl for "struct ClassName* this"
     *
     * Creates: struct ClassName* this
     * For use as first parameter in translated method.
     */
    clang::ParmVarDecl* createThisParameter(
        const std::string& className,
        HandlerContext& ctx
    );

    /**
     * @brief Translate method parameters to C parameters
     * @param cppMethod C++ method declaration
     * @param ctx Handler context
     * @return Vector of C parameter declarations
     *
     * Delegates to HandlerContext::translateType for type translation.
     */
    std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::CXXMethodDecl* cppMethod,
        HandlerContext& ctx
    );

    /**
     * @brief Get the class name for a method
     * @param cppMethod C++ method declaration
     * @return Class name as string
     */
    std::string getClassName(const clang::CXXMethodDecl* cppMethod) const;
};

} // namespace cpptoc
