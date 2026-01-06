/**
 * @file TypedefGenerator.h
 * @brief Phase 53: Generate C typedef declarations from C++ type aliases
 *
 * Generates C typedef AST nodes from analyzed type alias information.
 *
 * Design Principles:
 * - SOLID: Single Responsibility (typedef generation only)
 * - KISS: Simple API for generating typedefs
 * - DRY: Reusable typedef creation logic
 *
 * Usage Example:
 * @code
 *   TypedefGenerator generator(Context, Builder);
 *   TypeAliasInfo info = ...; // from TypeAliasAnalyzer
 *   TypedefDecl* typedefDecl = generator.generateTypedef(info);
 * @endcode
 */

#pragma once

#include "handlers/TypeAliasAnalyzer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Type.h"
#include "CNodeBuilder.h"
#include <string>

namespace cpptoc {

/**
 * @class TypedefGenerator
 * @brief Generates C typedef declarations from type alias information
 *
 * Handles:
 * - Simple typedefs: typedef int* IntPtr;
 * - Function pointer typedefs: typedef void (*Callback)(int);
 * - Struct typedefs: typedef struct Point Point2D;
 * - Array typedefs: typedef int IntArray[10];
 * - Const/volatile typedefs: typedef const int* ConstIntPtr;
 *
 * Translation Pattern:
 * C++: using IntPtr = int*;
 * C:   typedef int* IntPtr;
 *
 * C++: using Callback = void (*)(int, float);
 * C:   typedef void (*Callback)(int, float);
 */
class TypedefGenerator {
public:
    /**
     * @brief Construct a TypedefGenerator
     * @param Context Clang AST context
     * @param Builder C AST node builder
     */
    TypedefGenerator(clang::ASTContext& Context, clang::CNodeBuilder& Builder);

    /**
     * @brief Generate C typedef from type alias information
     * @param info TypeAliasInfo from TypeAliasAnalyzer
     * @return TypedefDecl* representing the C typedef (added to C TU)
     *
     * Creates a C typedef declaration with the following structure:
     * typedef <underlying_type> <alias_name>;
     *
     * Example:
     * info: aliasName="IntPtr", underlyingType=int*
     * → typedef int* IntPtr;
     */
    clang::TypedefDecl* generateTypedef(const TypeAliasInfo& info);

    /**
     * @brief Generate C typedef with explicit name and type
     * @param aliasName Name of the typedef
     * @param underlyingType Type being aliased
     * @return TypedefDecl* representing the C typedef
     *
     * Direct API for creating typedefs when you have explicit parameters.
     */
    clang::TypedefDecl* generateTypedef(
        const std::string& aliasName,
        clang::QualType underlyingType
    );

    /**
     * @brief Handle complex types (function pointers, arrays)
     * @param info TypeAliasInfo with complex underlying type
     * @return TypedefDecl* with proper complex type handling
     *
     * Function pointers require special handling:
     * C++: using Callback = void (*)(int, float);
     * C:   typedef void (*Callback)(int, float);
     *
     * Arrays also need special handling:
     * C++: using IntArray = int[10];
     * C:   typedef int IntArray[10];
     */
    clang::TypedefDecl* handleComplexType(const TypeAliasInfo& info);

    /**
     * @brief Generate typedef for function pointer type
     * @param aliasName Name of the typedef
     * @param funcPtrType Function pointer QualType
     * @return TypedefDecl* for function pointer typedef
     *
     * Pattern:
     * typedef <return_type> (*<alias_name>)(<params>);
     */
    clang::TypedefDecl* generateFunctionPointerTypedef(
        const std::string& aliasName,
        clang::QualType funcPtrType
    );

    /**
     * @brief Generate typedef for array type
     * @param aliasName Name of the typedef
     * @param arrayType Array QualType
     * @return TypedefDecl* for array typedef
     *
     * Pattern:
     * typedef <element_type> <alias_name>[<size>];
     */
    clang::TypedefDecl* generateArrayTypedef(
        const std::string& aliasName,
        clang::QualType arrayType
    );

    /**
     * @brief Check if a QualType is a complex type requiring special handling
     * @param Type QualType to check
     * @return true if Type is function pointer or array
     */
    bool isComplexType(clang::QualType Type);

private:
    clang::ASTContext& Context;
    clang::CNodeBuilder& Builder;

    /**
     * @brief Create TypedefDecl AST node
     * @param aliasName Name of the typedef
     * @param underlyingType Type being aliased
     * @param DC DeclContext for the typedef
     * @return TypedefDecl* AST node
     *
     * Low-level helper for creating typedef declarations.
     */
    clang::TypedefDecl* createTypedefDecl(
        const std::string& aliasName,
        clang::QualType underlyingType,
        clang::DeclContext* DC
    );
};

} // namespace cpptoc
