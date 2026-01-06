/**
 * @file MethodSignatureHelper.h
 * @brief Phase 31-03: Shared helper for generating C function signatures from C++ methods
 *
 * Extracts common signature generation logic used by both VtableGenerator and CppToCVisitor.
 * Follows DRY principle to avoid code duplication.
 */

#ifndef METHOD_SIGNATURE_HELPER_H
#define METHOD_SIGNATURE_HELPER_H

#include "clang/AST/DeclCXX.h"
#include <string>

/**
 * @class MethodSignatureHelper
 * @brief Helper class for generating C function signatures from C++ methods.
 *
 * Used by both VtableGenerator and CppToCVisitor to ensure consistency
 * in function signature generation across the codebase.
 *
 * SOLID Principles:
 * - Single Responsibility: Only generates signatures, nothing else
 * - Open/Closed: Extensible for new method types without modification
 * - Dependency Inversion: Depends on Clang abstractions, not concrete implementations
 *
 * Phase 31-04 Optimizations:
 * - Type string caching to avoid redundant AST queries
 * - Pre-allocated string buffers to reduce reallocations
 * - Cached method properties to minimize repeated checks
 */
class MethodSignatureHelper {
public:
    /**
     * @brief Clear all internal caches
     *
     * Should be called between translation units to prevent cache bloat.
     * Memory is automatically freed when cache is cleared.
     */
    static void clearCaches();
    /**
     * @brief Generate complete static function signature for a method
     * @param Method The C++ method to generate signature for
     * @param ClassName The name of the class containing the method
     * @return Complete C function signature with 'static' keyword
     *
     * Example: "static int Circle_getArea(struct Circle *this, int param)"
     *
     * Handles:
     * - Return type translation (C++ -> C)
     * - Method name mangling (constructors, destructors, overloads)
     * - 'this' parameter injection
     * - Parameter type translation
     * - Const correctness
     */
    static std::string generateSignature(const clang::CXXMethodDecl* Method,
                                         const std::string& ClassName);

    /**
     * @brief Get C type string from Clang QualType
     * @param Type Clang type to convert
     * @return C type string
     *
     * Handles:
     * - Primitive types (int, float, double, bool -> int)
     * - Pointers and const qualifiers
     * - References (converted to pointers in C)
     * - Class/struct types (prefixed with 'struct')
     */
    static std::string getTypeString(clang::QualType Type);

    /**
     * @brief Get mangled C function name for a C++ method
     * @param Method The C++ method to mangle
     * @param ClassName The name of the class containing the method
     * @return Mangled C function name
     *
     * Naming conventions:
     * - Constructor: ClassName__ctor[_N] where N is parameter count
     * - Destructor: ClassName__dtor
     * - Regular method: ClassName_methodName[_suffix] for overloads
     */
    static std::string getMangledName(const clang::CXXMethodDecl* Method,
                                      const std::string& ClassName);

    /**
     * @brief Check if 'this' parameter should be const
     * @param Method The C++ method to check
     * @return true if method is const-qualified
     */
    static bool isConstMethod(const clang::CXXMethodDecl* Method);

private:
    /**
     * @brief Generate mangled suffix for overloaded methods
     * @param Method The method to generate suffix for
     * @return Suffix based on parameter types, or empty string if not overloaded
     *
     * Phase 40 (Bug Fix): Now includes full type-based mangling for cross-file consistency
     */
    static std::string generateOverloadSuffix(const clang::CXXMethodDecl* Method);

    /**
     * @brief Get simple type name for mangling purposes
     * @param T The type to simplify
     * @return Simplified type name (e.g., "const_Vector3D_ref", "int", "float_ptr")
     *
     * Phase 40 (Bug Fix): Used for generating parameter type suffixes in method names
     * Ensures cross-file consistency in method name generation
     */
    static std::string getSimpleTypeName(clang::QualType T);
};

#endif // METHOD_SIGNATURE_HELPER_H
