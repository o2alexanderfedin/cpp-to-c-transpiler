/**
 * @file TypeInfoGenerator.cpp
 * @brief Story #83: type_info Structure Generation (Itanium ABI) Implementation
 *
 * Generates type_info structures following the Itanium C++ ABI specification.
 * Implements the three type_info classes based on inheritance patterns.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only generates type_info structures
 * - Open/Closed: Extensible for new type_info variants without modification
 * - Liskov Substitution: Type info classes follow Itanium ABI hierarchy
 * - Interface Segregation: Clean public API, private implementation details
 * - Dependency Inversion: Depends on Clang AST abstractions, not concrete types
 */

#include "TypeInfoGenerator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include <sstream>

using namespace clang;

/**
 * @brief Constructor with AST context and virtual method analyzer
 */
TypeInfoGenerator::TypeInfoGenerator(ASTContext& Context, VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(&Analyzer) {}

/**
 * @brief Constructor with AST context only (for testing)
 */
TypeInfoGenerator::TypeInfoGenerator(ASTContext& Context)
    : Context(Context), Analyzer(nullptr) {}

/**
 * @brief Generate type_info constant for a polymorphic class
 *
 * Only generates type_info for polymorphic classes (classes with virtual functions).
 * Non-polymorphic classes don't have RTTI and return empty string.
 *
 * @param Record Class to generate type_info for
 * @return C code for type_info constant, or empty string if not polymorphic
 */
std::string TypeInfoGenerator::generateTypeInfo(const CXXRecordDecl* Record) {
    if (!Record || !Record->isCompleteDefinition()) {
        return "";
    }

    // Only polymorphic classes have RTTI
    if (!isPolymorphic(Record)) {
        return "";
    }

    // Determine which type_info class to use
    TypeInfoClass tiClass = getTypeInfoClass(Record);

    // Generate appropriate type_info structure
    switch (tiClass) {
        case TypeInfoClass::CLASS_TYPE_INFO:
            return generateClassTypeInfo(Record);
        case TypeInfoClass::SI_CLASS_TYPE_INFO:
            return generateSIClassTypeInfo(Record);
        case TypeInfoClass::VMI_CLASS_TYPE_INFO:
            return generateVMIClassTypeInfo(Record);
    }

    return "";
}

/**
 * @brief Determine which type_info class to use based on inheritance
 *
 * Itanium ABI rules:
 * - __class_type_info: No base classes
 * - __si_class_type_info: Exactly one public non-virtual base class
 * - __vmi_class_type_info: Multiple inheritance or virtual inheritance
 *
 * @param Record Class to analyze
 * @return Type of type_info class
 */
TypeInfoClass TypeInfoGenerator::getTypeInfoClass(const CXXRecordDecl* Record) {
    if (!Record) {
        return TypeInfoClass::CLASS_TYPE_INFO;
    }

    unsigned numBases = Record->getNumBases();

    // No bases: use __class_type_info
    if (numBases == 0) {
        return TypeInfoClass::CLASS_TYPE_INFO;
    }

    // Check for virtual inheritance
    for (const auto& Base : Record->bases()) {
        if (Base.isVirtual()) {
            // Virtual inheritance requires __vmi_class_type_info
            return TypeInfoClass::VMI_CLASS_TYPE_INFO;
        }
    }

    // Single non-virtual base: use __si_class_type_info
    if (numBases == 1) {
        return TypeInfoClass::SI_CLASS_TYPE_INFO;
    }

    // Multiple inheritance: use __vmi_class_type_info
    return TypeInfoClass::VMI_CLASS_TYPE_INFO;
}

/**
 * @brief Generate type_info structure definitions (headers)
 *
 * Generates the three type_info struct definitions per Itanium ABI.
 * These should be included in the generated C header file.
 *
 * @return C code for type_info struct definitions
 */
std::string TypeInfoGenerator::generateTypeInfoStructs() {
    std::stringstream ss;

    ss << "// ============================================================================\n";
    ss << "// Type Info Structures (Itanium C++ ABI)\n";
    ss << "// ============================================================================\n\n";

    // Base type_info class
    ss << "/**\n";
    ss << " * @brief Base class for all class type_info (Itanium ABI)\n";
    ss << " * Used for classes with no inheritance\n";
    ss << " */\n";
    ss << "struct __class_type_info {\n";
    ss << "    const void *vtable_ptr;    /**< Pointer to type_info vtable */\n";
    ss << "    const char *type_name;     /**< Length-prefixed type name */\n";
    ss << "};\n\n";

    // Single inheritance type_info
    ss << "/**\n";
    ss << " * @brief Type info for single inheritance (Itanium ABI)\n";
    ss << " * Used for classes with exactly one non-virtual base\n";
    ss << " */\n";
    ss << "struct __si_class_type_info {\n";
    ss << "    const void *vtable_ptr;                        /**< Pointer to type_info vtable */\n";
    ss << "    const char *type_name;                         /**< Length-prefixed type name */\n";
    ss << "    const struct __class_type_info *base_type;     /**< Pointer to base type_info */\n";
    ss << "};\n\n";

    // Virtual/multiple inheritance type_info
    ss << "/**\n";
    ss << " * @brief Base class type info for multiple/virtual inheritance (Itanium ABI)\n";
    ss << " */\n";
    ss << "struct __base_class_type_info {\n";
    ss << "    const struct __class_type_info *base_type;  /**< Pointer to base type_info */\n";
    ss << "    long offset_flags;                          /**< Offset (bits 8+) and flags (bits 0-7) */\n";
    ss << "};\n\n";

    ss << "/**\n";
    ss << " * @brief Type info for virtual/multiple inheritance (Itanium ABI)\n";
    ss << " * Used for classes with multiple bases or virtual inheritance\n";
    ss << " */\n";
    ss << "struct __vmi_class_type_info {\n";
    ss << "    const void *vtable_ptr;                     /**< Pointer to type_info vtable */\n";
    ss << "    const char *type_name;                      /**< Length-prefixed type name */\n";
    ss << "    unsigned int flags;                         /**< Inheritance flags */\n";
    ss << "    unsigned int base_count;                    /**< Number of base classes */\n";
    ss << "    struct __base_class_type_info base_info[1]; /**< Variable-length array of bases */\n";
    ss << "};\n\n";

    // External vtable declarations
    ss << "// External vtable pointers (defined in runtime)\n";
    ss << "extern const void *__vt_class_type_info;\n";
    ss << "extern const void *__vt_si_class_type_info;\n";
    ss << "extern const void *__vt_vmi_class_type_info;\n\n";

    return ss.str();
}

/**
 * @brief Encode type name per Itanium ABI (length-prefixed)
 *
 * Itanium ABI uses length-prefixed names: length + name
 * Example: "Base" -> "4Base", "Derived" -> "7Derived"
 *
 * @param ClassName Name of the class
 * @return Length-prefixed type name
 */
std::string TypeInfoGenerator::encodeTypeName(const std::string& ClassName) {
    std::stringstream ss;
    ss << ClassName.length() << ClassName;
    return ss.str();
}

/**
 * @brief Generate __class_type_info constant (no inheritance)
 *
 * @param Record Class record
 * @return C code for __class_type_info constant
 */
std::string TypeInfoGenerator::generateClassTypeInfo(const CXXRecordDecl* Record) {
    std::string className = Record->getNameAsString();
    std::string typeName = encodeTypeName(className);
    std::string varName = getTypeInfoVarName(className);

    std::stringstream ss;
    ss << "// Type info for " << className << " (no inheritance)\n";
    ss << "const struct __class_type_info " << varName << " = {\n";
    ss << "    .vtable_ptr = &__vt_class_type_info,\n";
    ss << "    .type_name = \"" << typeName << "\"\n";
    ss << "};\n";

    return ss.str();
}

/**
 * @brief Generate __si_class_type_info constant (single inheritance)
 *
 * @param Record Class record
 * @return C code for __si_class_type_info constant
 */
std::string TypeInfoGenerator::generateSIClassTypeInfo(const CXXRecordDecl* Record) {
    std::string className = Record->getNameAsString();
    std::string typeName = encodeTypeName(className);
    std::string varName = getTypeInfoVarName(className);

    // Get base class
    const CXXBaseSpecifier* firstBase = nullptr;
    if (Record->getNumBases() > 0) {
        firstBase = Record->bases_begin();
    }

    std::string baseTypeName;
    if (firstBase) {
        const CXXRecordDecl* BaseRecord = firstBase->getType()->getAsCXXRecordDecl();
        if (BaseRecord) {
            baseTypeName = getTypeInfoVarName(BaseRecord->getNameAsString());
        }
    }

    std::stringstream ss;
    ss << "// Type info for " << className << " (single inheritance)\n";
    ss << "const struct __si_class_type_info " << varName << " = {\n";
    ss << "    .vtable_ptr = &__vt_si_class_type_info,\n";
    ss << "    .type_name = \"" << typeName << "\",\n";
    ss << "    .base_type = &" << baseTypeName << "\n";
    ss << "};\n";

    return ss.str();
}

/**
 * @brief Generate __vmi_class_type_info constant (virtual/multiple inheritance)
 *
 * @param Record Class record
 * @return C code for __vmi_class_type_info constant
 */
std::string TypeInfoGenerator::generateVMIClassTypeInfo(const CXXRecordDecl* Record) {
    std::string className = Record->getNameAsString();
    std::string typeName = encodeTypeName(className);
    std::string varName = getTypeInfoVarName(className);

    unsigned numBases = Record->getNumBases();

    std::stringstream ss;
    ss << "// Type info for " << className << " (virtual/multiple inheritance)\n";
    ss << "const struct __vmi_class_type_info " << varName << " = {\n";
    ss << "    .vtable_ptr = &__vt_vmi_class_type_info,\n";
    ss << "    .type_name = \"" << typeName << "\",\n";
    ss << "    .flags = 0,\n";
    ss << "    .base_count = " << numBases << ",\n";
    ss << "    .base_info = {\n";

    // Generate base class entries
    unsigned baseIndex = 0;
    for (const auto& Base : Record->bases()) {
        const CXXRecordDecl* BaseRecord = Base.getType()->getAsCXXRecordDecl();
        if (!BaseRecord) continue;

        std::string baseVarName = getTypeInfoVarName(BaseRecord->getNameAsString());

        // Calculate offset (simplified - actual implementation would use ASTRecordLayout)
        // For now, use baseIndex * 8 as a placeholder offset in bits 8+
        long offsetFlags = (baseIndex * 8) << 8;

        ss << "        {.base_type = &" << baseVarName << ", .offset_flags = " << offsetFlags << "}";

        if (baseIndex < numBases - 1) {
            ss << ",";
        }
        ss << "\n";

        baseIndex++;
    }

    ss << "    }\n";
    ss << "};\n";

    return ss.str();
}

/**
 * @brief Get type_info variable name for a class
 *
 * Convention: __ti_<ClassName>
 *
 * @param ClassName Name of the class
 * @return Type_info variable name
 */
std::string TypeInfoGenerator::getTypeInfoVarName(const std::string& ClassName) {
    return "__ti_" + ClassName;
}

/**
 * @brief Check if class is polymorphic (has virtual functions)
 *
 * Uses VirtualMethodAnalyzer if available, otherwise checks AST directly.
 *
 * @param Record Class record
 * @return True if polymorphic, false otherwise
 */
bool TypeInfoGenerator::isPolymorphic(const CXXRecordDecl* Record) {
    if (!Record) {
        return false;
    }

    // Use analyzer if available
    if (Analyzer) {
        return Analyzer->isPolymorphic(Record);
    }

    // Fallback: check AST directly
    return Record->isPolymorphic();
}
