/**
 * @file VariableHandler.h
 * @brief Handler for translating C++ variables to C variables
 *
 * Translates C++ variable declarations (VarDecl) to equivalent C variable
 * declarations. Handles type translation, initialization expressions, and
 * storage class specifiers.
 *
 * Scope (Phase 1):
 * - Local variables with basic types
 * - Global variables
 * - Static variables
 * - Extern variables
 * - Const variables
 * - Pointer variables
 * - Initialization with literals
 *
 * Out of Scope (Future):
 * - Reference variables (Phase 2)
 * - Member variables (handled by ClassToStructTranslator)
 * - Array variables (Phase 2)
 * - Complex initialization (Phase 2)
 * - Constexpr variables (Phase 3)
 */

#pragma once

#include "handlers/ASTHandler.h"

namespace cpptoc {

/**
 * @class VariableHandler
 * @brief Translates C++ variable declarations to C variable declarations
 *
 * Example Translations:
 * C++: int x = 42;
 * C:   int x = 42;
 *
 * C++: const int MAX = 100;
 * C:   const int MAX = 100;
 *
 * C++: static int counter = 0;
 * C:   static int counter = 0;
 */
class VariableHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes variable declarations
     * @param D Declaration to check
     * @return true if D is a VarDecl (but not a member variable)
     */
    bool canHandle(const clang::Decl* D) const override;

    /**
     * @brief Translate C++ variable to C variable
     * @param D C++ VarDecl
     * @param ctx Handler context
     * @return C VarDecl
     *
     * Translation Process:
     * 1. Extract variable properties (name, type, storage class)
     * 2. Translate type using context
     * 3. Translate initialization expression (if present)
     * 4. Create C VarDecl with CNodeBuilder
     * 5. Register mapping in context
     */
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;

private:
    /**
     * @brief Translate C++ type to C type
     * @param cppType C++ type
     * @param ctx Handler context
     * @return C type (with reference types converted to pointers)
     *
     * Translation rules:
     * - T& (lvalue reference) → T*
     * - T&& (rvalue reference) → T*
     * - const T& → const T*
     * - T*& → T**
     * - All other types → unchanged
     */
    clang::QualType translateType(
        clang::QualType cppType,
        HandlerContext& ctx
    );

    /**
     * @brief Translate variable initialization expression
     * @param init C++ initialization expression
     * @param ctx Handler context
     * @return C initialization expression, or nullptr if no init
     *
     * For Phase 1, simply passes through literal expressions.
     * Phase 2 will handle complex expressions via ExpressionHandler.
     */
    clang::Expr* translateInitializer(
        const clang::Expr* init,
        HandlerContext& ctx
    );

    /**
     * @brief Translate storage class specifier
     * @param sc C++ storage class
     * @return C storage class
     *
     * Most storage classes map directly:
     * - SC_None → SC_None
     * - SC_Static → SC_Static
     * - SC_Extern → SC_Extern
     * - SC_Auto → SC_None (auto is implicit in C)
     */
    clang::StorageClass translateStorageClass(clang::StorageClass sc);
};

} // namespace cpptoc
