/**
 * @file FunctionHandler.h
 * @brief Handler for translating C++ functions to C functions
 *
 * Translates simple C++ free functions (not methods) to equivalent C functions.
 * Handles parameter translation, return types, and function bodies.
 *
 * Scope (Phase 1):
 * - Simple functions with basic types
 * - Parameters (no default values)
 * - Return types
 * - Function bodies (delegated to StatementHandler)
 *
 * Out of Scope (Future):
 * - Methods (handled by MethodHandler)
 * - Constructors/Destructors
 * - Templates (handled by TemplateMonomorphizer)
 * - Default parameters
 * - Function overloading
 */

#pragma once

#include "handlers/ASTHandler.h"

namespace cpptoc {

/**
 * @class FunctionHandler
 * @brief Translates C++ free functions to C functions
 *
 * Example Translation:
 * C++: int add(int a, int b) { return a + b; }
 * C:   int add(int a, int b) { return a + b; }
 */
class FunctionHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes function declarations
     */
    bool canHandle(const clang::Decl* D) const override;

    /**
     * @brief Translate C++ function to C function
     * @param D C++ FunctionDecl
     * @param ctx Handler context
     * @return C FunctionDecl
     */
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;

private:
    /**
     * @brief Translate function parameters
     */
    std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::FunctionDecl* cppFunc,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
