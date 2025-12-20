/**
 * @file RvalueRefParamTranslator.h
 * @brief Rvalue Reference Parameter Detection and Translation to C (Story #133)
 *
 * Responsibilities (Single Responsibility Principle):
 * - Detect rvalue reference types in function parameters
 * - Translate rvalue reference parameters to C pointer types
 * - Translate function signatures with rvalue reference parameters
 * - Handle const-correctness for rvalue references
 * - Integration with existing type translation infrastructure
 *
 * Design Principles:
 * - SOLID: Single responsibility, open for extension
 * - DRY: Reuse existing type translation patterns
 * - KISS: Simple, clear API for parameter type translation
 *
 * Story Context:
 * - Builds on Stories #130-132 (move semantics infrastructure)
 * - Focuses on parameter type translation in function signatures
 * - Call site translation handled separately
 *
 * Translation Strategy:
 * - C++: void func(Buffer&& b)    → C: void func(struct Buffer *b)
 * - C++: void func(const Buffer&& b) → C: void func(const struct Buffer *b)
 * - C++: Buffer&& getBuffer()     → C: struct Buffer* getBuffer()
 * - Primitives: int&& → int (passed by value, implementation choice)
 */

#ifndef RVALUE_REF_PARAM_TRANSLATOR_H
#define RVALUE_REF_PARAM_TRANSLATOR_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include <string>

class RvalueRefParamTranslator {
public:
    /**
     * Constructor
     * @param Context Clang AST context for type queries and traversal
     */
    explicit RvalueRefParamTranslator(clang::ASTContext& Context);

    /**
     * Detect if type is rvalue reference
     *
     * Checks QualType to determine if it is an rvalue reference type (T&&).
     * Note: This does NOT distinguish between rvalue references and forwarding
     * references (T&& in template context). Forwarding reference detection
     * requires template instantiation analysis (marked as future work).
     *
     * @param Type The QualType to check
     * @return true if type is rvalue reference (T&&)
     */
    bool isRvalueReference(const clang::QualType& Type) const;

    /**
     * Translate rvalue reference type to C pointer type
     *
     * Translation rules:
     * - Buffer&& → struct Buffer *
     * - const Buffer&& → const struct Buffer *
     * - int&& → int (primitives passed by value)
     *
     * The translation preserves const-correctness and handles both
     * class types and primitive types appropriately.
     *
     * @param Type The rvalue reference QualType to translate
     * @return C type string (e.g., "struct Buffer *", "const struct Buffer *")
     */
    std::string translateType(const clang::QualType& Type);

    /**
     * Translate function parameter with potential rvalue reference type
     *
     * Generates complete C parameter declaration including type and name.
     * Example: Buffer&& b → struct Buffer *b
     *
     * @param Param Parameter declaration to translate
     * @return C parameter string (e.g., "struct Buffer *b")
     */
    std::string translateParameter(const clang::ParmVarDecl* Param);

    /**
     * Translate entire function signature
     *
     * Generates complete C function signature including return type,
     * function name, and all parameters with proper translations.
     *
     * Example:
     *   C++: Buffer&& process(Buffer&& a, const Buffer& b)
     *   C:   struct Buffer* process(struct Buffer *a, const struct Buffer *b)
     *
     * @param Func Function declaration to translate
     * @return Complete C function signature
     */
    std::string translateFunctionSignature(const clang::FunctionDecl* Func);

private:
    clang::ASTContext& Context;

    /**
     * Strip rvalue reference, return base type
     *
     * Given Buffer&&, returns Buffer.
     * Given const Buffer&&, returns const Buffer.
     *
     * @param RvalueRefType Rvalue reference QualType
     * @return Base type without rvalue reference
     */
    clang::QualType getBaseType(const clang::QualType& RvalueRefType);

    /**
     * Check if rvalue reference is const
     *
     * Determines if the rvalue reference has const qualifier.
     * Example: const Buffer&& → true, Buffer&& → false
     *
     * @param Type Rvalue reference QualType
     * @return true if const rvalue reference
     */
    bool isConstRvalueRef(const clang::QualType& Type) const;

    /**
     * Check if type is primitive (non-class type)
     *
     * Primitive types (int, float, etc.) are handled differently
     * from class types in the translation.
     *
     * @param Type QualType to check
     * @return true if type is primitive (int, float, char, etc.)
     */
    bool isPrimitiveType(const clang::QualType& Type) const;

    /**
     * Get class/struct name from type
     *
     * Extracts the class or struct name from a QualType.
     * Example: Buffer → "Buffer", std::vector<int> → "vector"
     *
     * @param Type QualType to extract name from
     * @return Class/struct name as string
     */
    std::string getClassName(const clang::QualType& Type) const;

    /**
     * Translate non-rvalue-reference type
     *
     * Delegates to existing type translation for non-rvalue-reference types.
     * This ensures consistency with the rest of the type translation system.
     *
     * @param Type QualType to translate
     * @return C type string
     */
    std::string translateNonRvalueRefType(const clang::QualType& Type);
};

#endif // RVALUE_REF_PARAM_TRANSLATOR_H
