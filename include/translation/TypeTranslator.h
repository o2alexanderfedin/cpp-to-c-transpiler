/**
 * @file TypeTranslator.h
 * @brief Utility for translating C++ types to C-compatible types
 *
 * Provides type translation services for the transpiler:
 * - C++ references (T&, T&&) → C pointers (T*)
 * - Future: Handle other C++ type constructs (auto, decltype, etc.)
 *
 * This is a UTILITY class, not a handler:
 * - Handlers process AST nodes via dispatcher
 * - TypeTranslator is a service used by handlers
 */

#pragma once

#include "clang/AST/Type.h"
#include "clang/AST/ASTContext.h"

namespace cpptoc {

/**
 * @class TypeTranslator
 * @brief Translates C++ types to C-compatible equivalents
 *
 * Single Responsibility: Type translation only
 * Used by FunctionHandler, ParameterHandler, and future handlers
 */
class TypeTranslator {
public:
    /**
     * @brief Translate C++ type to C-compatible type
     * @param cppType C++ type to translate
     * @param cASTContext Target C ASTContext for creating types
     * @return C-compatible QualType
     *
     * Translation rules:
     * - T& → T* (lvalue reference to pointer)
     * - T&& → T* (rvalue reference to pointer, C has no move semantics)
     * - Other types pass through unchanged (for now)
     *
     * Note: If cross-ASTContext type errors occur, will need to recreate
     * types in cASTContext instead of passing through.
     */
    static clang::QualType translateType(
        clang::QualType cppType,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
