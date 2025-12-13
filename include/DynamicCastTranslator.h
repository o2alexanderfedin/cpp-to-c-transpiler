/**
 * @file DynamicCastTranslator.h
 * @brief Story #85: dynamic_cast Downcast Support
 *
 * Translates C++ dynamic_cast expressions to runtime cxx_dynamic_cast() calls in C.
 * Implements safe downcasting with runtime type checking.
 *
 * SOLID Principles:
 * - Single Responsibility: Translates dynamic_cast expressions only
 * - Open/Closed: Extensible for cross-casting (Story #87)
 * - Interface Segregation: Clean public API
 * - Dependency Inversion: Depends on Clang AST abstractions
 */

#ifndef DYNAMIC_CAST_TRANSLATOR_H
#define DYNAMIC_CAST_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include "TypeInfoGenerator.h"
#include <string>

/**
 * @class DynamicCastTranslator
 * @brief Translates C++ dynamic_cast operator to C runtime cxx_dynamic_cast() calls
 *
 * The dynamic_cast operator performs safe type casting with runtime type checking.
 * It returns nullptr if the cast fails (object is not of the target type).
 *
 * C++ Example:
 * Base* base_ptr = new Derived();
 * Derived* d = dynamic_cast<Derived*>(base_ptr);  // Success - returns Derived*
 * Other* o = dynamic_cast<Other*>(base_ptr);      // Fails - returns nullptr
 *
 * C Translation:
 * struct Base *base_ptr = ...;
 *
 * // Successful downcast
 * struct Derived *d = (struct Derived*)cxx_dynamic_cast(
 *     base_ptr,
 *     &__ti_Base,     // Source type_info
 *     &__ti_Derived,  // Target type_info
 *     -1              // Offset (-1 = runtime check required)
 * );
 *
 * // Failed downcast (different hierarchy) - returns NULL
 * struct Other *o = (struct Other*)cxx_dynamic_cast(
 *     base_ptr,
 *     &__ti_Base,
 *     &__ti_Other,
 *     -1
 * );
 *
 * Runtime function signature:
 * void* cxx_dynamic_cast(const void *ptr,
 *                        const struct __class_type_info *src_type,
 *                        const struct __class_type_info *dst_type,
 *                        ptrdiff_t offset);
 */
class DynamicCastTranslator {
public:
    /**
     * @brief Construct translator with AST context and virtual method analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer for polymorphism detection
     */
    DynamicCastTranslator(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Translate dynamic_cast expression to C cxx_dynamic_cast() call
     * @param CastExpr dynamic_cast expression to translate
     * @return C code for cxx_dynamic_cast() call
     */
    std::string translateDynamicCast(const clang::CXXDynamicCastExpr* CastExpr);

    /**
     * @brief Get source type name from cast expression
     * @param CastExpr dynamic_cast expression
     * @return Source type name (e.g., "Base")
     */
    std::string getSourceTypeName(const clang::CXXDynamicCastExpr* CastExpr);

    /**
     * @brief Get target type name from cast expression
     * @param CastExpr dynamic_cast expression
     * @return Target type name (e.g., "Derived")
     */
    std::string getTargetTypeName(const clang::CXXDynamicCastExpr* CastExpr);

private:
    /**
     * @brief Extract class name from QualType
     * @param Type Type to extract class name from
     * @return Class name string
     */
    std::string getClassName(clang::QualType Type);

    /**
     * @brief Generate cxx_dynamic_cast() function call
     * @param CastExpr Cast expression
     * @param SourceType Source type name
     * @param TargetType Target type name
     * @return C code for function call
     */
    std::string generateRuntimeCall(const clang::CXXDynamicCastExpr* CastExpr,
                                     const std::string& SourceType,
                                     const std::string& TargetType);

    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // DYNAMIC_CAST_TRANSLATOR_H
