/**
 * @file VtableGenerator.h
 * @brief Story #168: Vtable Struct Generation
 *
 * Generates vtable struct definitions for polymorphic classes.
 * Vtables contain function pointers for all virtual methods in a class,
 * with destructor always first, followed by virtual methods in declaration order.
 */

#ifndef VTABLE_GENERATOR_H
#define VTABLE_GENERATOR_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include <string>
#include <vector>

/**
 * @class VtableGenerator
 * @brief Generates C vtable struct definitions for polymorphic C++ classes
 *
 * Vtable structure:
 * - Destructor function pointer (always first)
 * - Virtual method function pointers in declaration order
 * - Override inherited methods (keep same slot)
 *
 * Example output:
 * struct Shape_vtable {
 *     void (*destructor)(struct Shape *this);
 *     double (*area)(struct Shape *this);
 *     void (*draw)(struct Shape *this);
 * };
 */
class VtableGenerator {
public:
    /**
     * @brief Construct generator with AST context and virtual method analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer for detecting polymorphic classes
     */
    VtableGenerator(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Generate vtable struct definition for a polymorphic class
     * @param Record Class to generate vtable for
     * @return C code for vtable struct, or empty string if not polymorphic
     */
    std::string generateVtableStruct(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get ordered list of methods for vtable
     * @param Record Class to analyze
     * @return Vector of methods in vtable order (destructor first, then virtual methods)
     */
    std::vector<clang::CXXMethodDecl*> getVtableMethodOrder(const clang::CXXRecordDecl* Record);

private:
    /**
     * @brief Generate function pointer declaration for a method
     * @param Method Method to generate pointer for
     * @param ClassName Name of the class (for 'this' parameter)
     * @return C function pointer declaration
     */
    std::string generateFunctionPointer(const clang::CXXMethodDecl* Method, const std::string& ClassName);

    /**
     * @brief Get C type string from Clang QualType
     * @param Type Clang type
     * @return C type string
     */
    std::string getTypeString(clang::QualType Type);

    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // VTABLE_GENERATOR_H
