/**
 * @file TypeAliasAnalyzer.h
 * @brief Phase 53: Analyze C++ type aliases (using declarations)
 *
 * Analyzes C++ type aliases and template type aliases to prepare them
 * for translation to C typedefs.
 *
 * Design Principles:
 * - SOLID: Single Responsibility (type alias analysis only)
 * - KISS: Simple API for analyzing type aliases
 * - DRY: Reusable type extraction logic
 *
 * Usage Example:
 * @code
 *   TypeAliasAnalyzer analyzer(Context, Builder);
 *   if (auto* aliasDecl = dyn_cast<TypeAliasDecl>(D)) {
 *     TypeAliasInfo info = analyzer.analyzeTypeAlias(aliasDecl);
 *     // info contains alias name, underlying type, etc.
 *   }
 * @endcode
 */

#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Type.h"
#include "CNodeBuilder.h"
#include <string>
#include <optional>

namespace cpptoc {

/**
 * @struct TypeAliasInfo
 * @brief Information extracted from a C++ type alias
 */
struct TypeAliasInfo {
    std::string aliasName;          ///< Name of the alias (e.g., "IntPtr")
    clang::QualType underlyingType; ///< Underlying type (e.g., int*)
    bool isTemplateAlias;           ///< True if this is a template type alias
    bool isPointerType;             ///< True if underlying type is pointer
    bool isFunctionPointer;         ///< True if underlying type is function pointer
    bool hasConstQualifier;         ///< True if underlying type is const-qualified
    bool hasVolatileQualifier;      ///< True if underlying type is volatile-qualified
};

/**
 * @class TypeAliasAnalyzer
 * @brief Analyzes C++ type aliases for translation to C typedefs
 *
 * This class analyzes:
 * - Simple type aliases: using IntPtr = int*;
 * - Pointer type aliases: using CharPtr = char*;
 * - Function pointer aliases: using Callback = void (*)(int);
 * - Struct/class type aliases: using Point = struct Point2D;
 * - Template type aliases: template<typename T> using Vec = std::vector<T>;
 *
 * Translation Pattern:
 * C++: using IntPtr = int*;
 * C:   typedef int* IntPtr;
 *
 * C++: template<typename T> using Vec = std::vector<T>;
 * C:   typedef struct vector_int Vec_int;  // per instantiation
 */
class TypeAliasAnalyzer {
public:
    /**
     * @brief Construct a TypeAliasAnalyzer
     * @param Context Clang AST context
     * @param Builder C AST node builder
     */
    TypeAliasAnalyzer(clang::ASTContext& Context, clang::CNodeBuilder& Builder);

    /**
     * @brief Analyze a type alias declaration
     * @param TAD TypeAliasDecl to analyze
     * @return TypeAliasInfo containing extracted information
     *
     * Extracts:
     * - Alias name
     * - Underlying type
     * - Type characteristics (pointer, function pointer, qualifiers)
     *
     * Example:
     * using IntPtr = int*;
     * → aliasName: "IntPtr", underlyingType: int*, isPointerType: true
     */
    TypeAliasInfo analyzeTypeAlias(const clang::TypeAliasDecl* TAD);

    /**
     * @brief Extract underlying type from a type alias
     * @param TAD TypeAliasDecl
     * @return QualType representing the underlying type
     *
     * Handles:
     * - Simple types: using X = int; → int
     * - Pointer types: using X = int*; → int*
     * - Qualified types: using X = const int*; → const int*
     * - Nested aliases: using Y = X; using X = int; → int
     */
    clang::QualType extractUnderlyingType(const clang::TypeAliasDecl* TAD);

    /**
     * @brief Check if a type alias is a template type alias
     * @param TAD TypeAliasDecl
     * @return true if this is a template type alias (has template parameters)
     *
     * Example:
     * template<typename T> using Vec = std::vector<T>; → true
     * using IntPtr = int*; → false
     */
    bool isTemplateTypeAlias(const clang::TypeAliasDecl* TAD);

    /**
     * @brief Analyze a template type alias declaration
     * @param TATD TypeAliasTemplateDecl to analyze
     * @return std::optional<TypeAliasInfo> if analysis succeeds
     *
     * Template type aliases require monomorphization:
     * C++: template<typename T> using Vec = std::vector<T>;
     *      Vec<int> v;
     * C:   typedef struct vector_int Vec_int;
     *      struct vector_int v;
     */
    std::optional<TypeAliasInfo> analyzeTemplateTypeAlias(
        const clang::TypeAliasTemplateDecl* TATD
    );

    /**
     * @brief Check if underlying type is a function pointer
     * @param Type QualType to check
     * @return true if Type is a function pointer type
     *
     * Example:
     * void (*callback)(int, float) → true
     * int* → false
     */
    bool isFunctionPointerType(clang::QualType Type);

    /**
     * @brief Check if underlying type is a pointer type
     * @param Type QualType to check
     * @return true if Type is a pointer type (excluding function pointers)
     *
     * Example:
     * int* → true
     * char* → true
     * void (*)(int) → false (function pointer, not data pointer)
     */
    bool isPointerType(clang::QualType Type);

    /**
     * @brief Get simple name for an alias (without namespace qualification)
     * @param TAD TypeAliasDecl
     * @return Simple name string
     *
     * Example:
     * namespace ns { using IntPtr = int*; } → "IntPtr" (not "ns::IntPtr")
     */
    std::string getAliasName(const clang::TypeAliasDecl* TAD);

private:
    clang::ASTContext& Context;
    clang::CNodeBuilder& Builder;

    /**
     * @brief Check if a type has const qualifier
     * @param Type QualType to check
     * @return true if Type is const-qualified
     */
    bool hasConstQualifier(clang::QualType Type);

    /**
     * @brief Check if a type has volatile qualifier
     * @param Type QualType to check
     * @return true if Type is volatile-qualified
     */
    bool hasVolatileQualifier(clang::QualType Type);

    /**
     * @brief Resolve type through aliases to find ultimate underlying type
     * @param Type QualType that may be an alias
     * @return QualType with all aliases resolved
     *
     * Handles chained aliases:
     * using A = int;
     * using B = A;
     * using C = B;
     * C → int (ultimate type)
     */
    clang::QualType resolveAliasChain(clang::QualType Type);
};

} // namespace cpptoc
