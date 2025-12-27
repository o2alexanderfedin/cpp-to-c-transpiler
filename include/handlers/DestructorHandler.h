/**
 * @file DestructorHandler.h
 * @brief Handler for translating C++ destructors to C cleanup functions
 *
 * Translates C++ destructors to C cleanup functions with explicit this parameter.
 * Destructors are translated to functions named ClassName_destroy(struct ClassName* this).
 *
 * Scope (Phase 44):
 * - Simple destructors with cleanup code
 * - Virtual destructors (ignore virtual keyword for now)
 * - Destructor bodies (delegated to StatementHandler/ExpressionHandler)
 *
 * Out of Scope (Future):
 * - Virtual destructor tables (Phase 45 - Inheritance)
 * - Destructor call injection (handled by StatementHandler)
 * - Base class destructor chaining (Phase 45 - Inheritance)
 */

#pragma once

#include "handlers/ASTHandler.h"

namespace cpptoc {

/**
 * @class DestructorHandler
 * @brief Translates C++ destructors to C cleanup functions
 *
 * Example Translation:
 * C++:
 *   class Counter {
 *       int count;
 *   public:
 *       ~Counter() { count = 0; }
 *   };
 *
 * C:
 *   struct Counter {
 *       int count;
 *   };
 *   void Counter_destroy(struct Counter* this) {
 *       this->count = 0;
 *   }
 *
 * Naming Convention:
 * - ClassName::~ClassName() → ClassName_destroy()
 * - Always named "destroy" (no overloading possible)
 *
 * This Parameter:
 * - Always added as first parameter: struct ClassName* this
 * - Type: pointer to struct of class type
 *
 * Virtual Destructors (Phase 44):
 * - Virtual keyword is ignored
 * - Translated as regular function
 * - Phase 45 will add vtable support
 */
class DestructorHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes destructor declarations
     * @param D Declaration to check
     * @return true if D is a CXXDestructorDecl
     */
    bool canHandle(const clang::Decl* D) const override;

    /**
     * @brief Translate C++ destructor to C cleanup function
     * @param D C++ CXXDestructorDecl
     * @param ctx Handler context
     * @return C FunctionDecl representing cleanup function
     *
     * Translation Process:
     * 1. Extract class name from destructor
     * 2. Create function name: ClassName_destroy
     * 3. Create this parameter: struct ClassName* this
     * 4. Set return type: void
     * 5. Translate destructor body (delegated to handlers)
     * 6. Register mapping in context
     * 7. Return C FunctionDecl
     *
     * Note: Destructor body translation uses existing statement/expression handlers.
     */
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;

private:
    /**
     * @brief Create this parameter for destructor function
     * @param classType Type of the class
     * @param ctx Handler context
     * @return ParmVarDecl for this parameter
     *
     * Creates: struct ClassName* this
     */
    clang::ParmVarDecl* createThisParameter(
        clang::QualType classType,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
