/**
 * @file TypeHandler.h
 * @brief Handler for processing Type nodes (reference types)
 *
 * Registers with CppToCVisitorDispatcher to handle C++ type translations.
 * Translates reference types (LValueReferenceType, RValueReferenceType) to C pointer types.
 *
 * Phase 1 Scope: Reference type translation ONLY
 * - T& → T* (lvalue reference to pointer)
 * - T&& → T* (rvalue reference to pointer)
 * - Other types passed through unchanged (for now)
 *
 * Future Phases:
 * - auto, decltype type translation
 * - Template type translation
 * - Complex type constructs
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Type.h"

namespace cpptoc {

/**
 * @class TypeHandler
 * @brief Processes Type and creates C-compatible types
 *
 * Responsibilities:
 * - Match LValueReferenceType and RValueReferenceType (predicate)
 * - Translate references to C pointers
 * - Create C PointerType with appropriate pointee type
 * - Store type mapping in TypeMapper
 * - Pass through other types unchanged
 *
 * Translation Examples:
 * C++:  int&        → C: int*
 * C++:  const int&  → C: const int*
 * C++:  int&&       → C: int*
 * C++:  int         → C: int (pass-through)
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, declMapper, typeMapper);
 * TypeHandler::registerWith(dispatcher);
 *
 * const Type* cppType = ...;
 * dispatcher.dispatch(cppCtx, cCtx, const_cast<Type*>(cppType));
 * // → Creates C PointerType and stores in TypeMapper
 *
 * // Retrieve translated type
 * QualType cType = dispatcher.getTypeMapper().getCreatedType(cppType);
 * @endcode
 */
class TypeHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for Type nodes
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if type is a reference type
     * @param T Type to check (must not be null)
     * @return true if T is LValueReferenceType or RValueReferenceType
     *
     * Implementation pattern:
     * 1. Assert T is not null (fails fast on programming errors)
     * 2. Check for LValueReferenceType or RValueReferenceType
     *
     * @pre T != nullptr (asserted)
     */
    static bool canHandle(const clang::Type* T);

    /**
     * @brief Visitor: Translate C++ type to C type
     * @param disp Dispatcher for accessing TypeMapper
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param T Type to process (must not be null)
     *
     * Algorithm:
     * 1. Assert T is not null
     * 2. Check if T is LValueReferenceType or RValueReferenceType
     * 3. If reference type:
     *    - Extract pointee type
     *    - Create C PointerType with pointee type
     *    - Store mapping in TypeMapper
     * 4. If not reference type:
     *    - Pass through unchanged
     *    - Store identity mapping in TypeMapper
     * 5. Debug output for verification
     *
     * Phase 1 Limitation: Only handles reference types
     * - Other types (auto, decltype, templates) pass through unchanged
     * - This phase focuses on reference → pointer translation
     *
     * @pre T != nullptr (asserted)
     */
    static void handleType(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Type* T
    );
};

} // namespace cpptoc
