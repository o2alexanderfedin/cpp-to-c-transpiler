/**
 * @file TypeInfoGenerator.h
 * @brief Story #83: type_info Structure Generation (Itanium ABI)
 *
 * Generates type_info structures following the Itanium C++ ABI specification.
 * Three type_info classes are used based on inheritance complexity:
 * - __class_type_info: No inheritance
 * - __si_class_type_info: Single inheritance
 * - __vmi_class_type_info: Virtual or multiple inheritance
 *
 * SOLID Principles:
 * - Single Responsibility: Generates type_info structures only
 * - Open/Closed: Extensible for new type_info variants
 * - Interface Segregation: Clean API for type_info generation
 * - Dependency Inversion: Depends on Clang AST abstractions
 */

#ifndef TYPE_INFO_GENERATOR_H
#define TYPE_INFO_GENERATOR_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include <string>
#include <vector>

/**
 * @enum TypeInfoClass
 * @brief Type of type_info class to use based on inheritance pattern
 */
enum class TypeInfoClass {
    CLASS_TYPE_INFO,     ///< __class_type_info: No inheritance
    SI_CLASS_TYPE_INFO,  ///< __si_class_type_info: Single inheritance
    VMI_CLASS_TYPE_INFO  ///< __vmi_class_type_info: Virtual/multiple inheritance
};

/**
 * @class TypeInfoGenerator
 * @brief Generates Itanium ABI type_info structures for polymorphic C++ classes
 *
 * Type info structures provide runtime type information for dynamic_cast and typeid.
 * The Itanium ABI defines three type_info classes:
 *
 * 1. __class_type_info (base class, no inheritance):
 *    struct __class_type_info {
 *        const void *vtable_ptr;
 *        const char *type_name;
 *    };
 *
 * 2. __si_class_type_info (single inheritance):
 *    struct __si_class_type_info {
 *        const void *vtable_ptr;
 *        const char *type_name;
 *        const struct __class_type_info *base_type;
 *    };
 *
 * 3. __vmi_class_type_info (virtual/multiple inheritance):
 *    struct __vmi_class_type_info {
 *        const void *vtable_ptr;
 *        const char *type_name;
 *        unsigned flags;
 *        unsigned base_count;
 *        struct __base_class_type_info {
 *            const struct __class_type_info *base_type;
 *            long offset_flags;
 *        } bases[];
 *    };
 *
 * Example output:
 * const struct __class_type_info __ti_Base = {
 *     .vtable_ptr = &__vt_class_type_info,
 *     .type_name = "4Base"  // Length-prefixed (Itanium ABI)
 * };
 *
 * const struct __si_class_type_info __ti_Derived = {
 *     .vtable_ptr = &__vt_si_class_type_info,
 *     .type_name = "7Derived",
 *     .base_type = &__ti_Base
 * };
 */
class TypeInfoGenerator {
public:
    /**
     * @brief Construct generator with AST context and virtual method analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer for detecting polymorphic classes
     */
    TypeInfoGenerator(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Construct generator with AST context only (for testing)
     * @param Context Clang AST context
     */
    explicit TypeInfoGenerator(clang::ASTContext& Context);

    /**
     * @brief Generate type_info constant for a polymorphic class
     * @param Record Class to generate type_info for
     * @return C code for type_info constant, or empty string if not polymorphic
     */
    std::string generateTypeInfo(const clang::CXXRecordDecl* Record);

    /**
     * @brief Determine which type_info class to use based on inheritance
     * @param Record Class to analyze
     * @return Type of type_info class (CLASS_TYPE_INFO, SI_CLASS_TYPE_INFO, or VMI_CLASS_TYPE_INFO)
     */
    TypeInfoClass getTypeInfoClass(const clang::CXXRecordDecl* Record);

    /**
     * @brief Generate type_info structure definitions (headers)
     * @return C code for type_info struct definitions
     */
    std::string generateTypeInfoStructs();

private:
    /**
     * @brief Encode type name per Itanium ABI (length-prefixed)
     * @param ClassName Name of the class
     * @return Length-prefixed type name (e.g., "4Base")
     */
    std::string encodeTypeName(const std::string& ClassName);

    /**
     * @brief Generate __class_type_info constant
     * @param Record Class record
     * @return C code for __class_type_info constant
     */
    std::string generateClassTypeInfo(const clang::CXXRecordDecl* Record);

    /**
     * @brief Generate __si_class_type_info constant
     * @param Record Class record
     * @return C code for __si_class_type_info constant
     */
    std::string generateSIClassTypeInfo(const clang::CXXRecordDecl* Record);

    /**
     * @brief Generate __vmi_class_type_info constant
     * @param Record Class record
     * @return C code for __vmi_class_type_info constant
     */
    std::string generateVMIClassTypeInfo(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get type_info variable name for a class
     * @param ClassName Name of the class
     * @return Type_info variable name (e.g., "__ti_Base")
     */
    std::string getTypeInfoVarName(const std::string& ClassName);

    /**
     * @brief Check if class is polymorphic (has virtual functions)
     * @param Record Class record
     * @return True if polymorphic, false otherwise
     */
    bool isPolymorphic(const clang::CXXRecordDecl* Record);

    clang::ASTContext& Context;
    VirtualMethodAnalyzer* Analyzer;  ///< Optional analyzer for polymorphism detection
};

#endif // TYPE_INFO_GENERATOR_H
