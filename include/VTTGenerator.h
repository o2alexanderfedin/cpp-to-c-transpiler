/**
 * @file VTTGenerator.h
 * @brief Story #91: VTT (Virtual Table Tables) Generation
 *
 * Generates VTT arrays for classes with virtual inheritance.
 * VTT provides correct vtable pointers during construction stages.
 * Follows Itanium C++ ABI specification for VTT structure and ordering.
 */

#ifndef VTT_GENERATOR_H
#define VTT_GENERATOR_H

#include "clang/AST/AST.h"
#include <string>
#include <vector>

// Forward declarations
class VirtualInheritanceAnalyzer;

/**
 * @class VTTGenerator
 * @brief Generates VTT (Virtual Table Tables) for classes with virtual inheritance
 *
 * VTT Structure (Itanium ABI):
 * 1. Primary virtual pointer (complete object vtable)
 * 2. Secondary VTTs (for non-virtual proper base classes)
 * 3. Secondary virtual pointers (construction vtables)
 * 4. Virtual VTTs (for virtual base classes)
 *
 * Example output:
 * const void* __vtt_Diamond[] = {
 *     &__vtable_Diamond_primary,
 *     &__vtable_Diamond_Left_base,
 *     &__vtable_Diamond_Right_base,
 *     &__vtable_Diamond_Base,
 * };
 */
class VTTGenerator {
public:
    /**
     * @brief Construct VTT generator with AST context and virtual inheritance analyzer
     * @param Context Clang AST context
     * @param ViAnalyzer Virtual inheritance analyzer
     */
    VTTGenerator(clang::ASTContext& Context, const VirtualInheritanceAnalyzer& ViAnalyzer);

    /**
     * @brief Generate VTT array for a class with virtual bases
     * @param Record Class to generate VTT for
     * @return C code for VTT array, or empty string if no virtual bases
     */
    std::string generateVTT(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get number of entries in VTT
     * @param Record Class to analyze
     * @return Number of VTT entries needed
     */
    size_t getVTTEntryCount(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get ordered list of VTT entries
     * @param Record Class to analyze
     * @return Vector of vtable reference strings in VTT order
     */
    std::vector<std::string> getVTTEntries(const clang::CXXRecordDecl* Record);

private:
    /**
     * @brief Generate VTT name for a class
     * @param Record Class
     * @return VTT name (e.g., "__vtt_ClassName")
     */
    std::string getVTTName(const clang::CXXRecordDecl* Record) const;

    /**
     * @brief Collect VTT entries following Itanium ABI ordering
     * @param Record Class to analyze
     * @param entries Output vector for VTT entries
     */
    void collectVTTEntries(const clang::CXXRecordDecl* Record,
                           std::vector<std::string>& entries);

    /**
     * @brief Add primary vtable entry (first in VTT)
     * @param Record Class
     * @param entries Output vector
     */
    void addPrimaryVtableEntry(const clang::CXXRecordDecl* Record,
                               std::vector<std::string>& entries);

    /**
     * @brief Add base constructor vtable entries
     * @param Record Class
     * @param entries Output vector
     */
    void addBaseConstructorEntries(const clang::CXXRecordDecl* Record,
                                    std::vector<std::string>& entries);

    /**
     * @brief Add virtual base vtable entries
     * @param Record Class
     * @param entries Output vector
     */
    void addVirtualBaseEntries(const clang::CXXRecordDecl* Record,
                               std::vector<std::string>& entries);

    /**
     * @brief Get vtable reference string
     * @param Record Class
     * @param suffix Optional suffix (e.g., "_base", "_primary")
     * @return Vtable reference (e.g., "&__vtable_ClassName")
     */
    std::string getVtableReference(const clang::CXXRecordDecl* Record,
                                    const std::string& suffix = "") const;

    clang::ASTContext& Context;
    const VirtualInheritanceAnalyzer& ViAnalyzer;
};

#endif // VTT_GENERATOR_H
