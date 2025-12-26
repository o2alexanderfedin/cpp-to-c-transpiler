/**
 * @file TemplateMonomorphizer.h
 * @brief Story #68: Template Monomorphization and Code Generation
 *
 * Converts C++ template instantiations into separate C code.
 * Performs type substitution, generates structs and methods with mangled names.
 */

#ifndef TEMPLATE_MONOMORPHIZER_H
#define TEMPLATE_MONOMORPHIZER_H

#include "clang/AST/AST.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include <string>
#include <map>
#include <vector>

/**
 * @class TemplateMonomorphizer
 * @brief Generates C AST nodes from template instantiations
 *
 * Takes ClassTemplateSpecializationDecl and FunctionDecl (template instantiations)
 * and generates equivalent C AST nodes (structs, functions) with proper type
 * substitution and name mangling.
 *
 * Phase 32.1: Refactored from string generation to AST generation for consistency
 * with overall transpiler architecture.
 *
 * Design: Single Responsibility - Only responsible for monomorphization
 */
class TemplateMonomorphizer {
public:
    /**
     * @brief Construct monomorphizer with AST context, name mangler, and AST builder
     * @param Context Clang AST context
     * @param Mangler Name mangler for generating unique C identifiers
     * @param Builder CNodeBuilder for creating C AST nodes
     */
    TemplateMonomorphizer(clang::ASTContext& Context, NameMangler& Mangler, clang::CNodeBuilder& Builder);

    /**
     * @brief Generate C struct AST node for a class template instantiation
     * @param D ClassTemplateSpecializationDecl
     * @return RecordDecl* representing the monomorphized struct (added to C TU)
     */
    clang::RecordDecl* monomorphizeClass(clang::ClassTemplateSpecializationDecl* D);

    /**
     * @brief Generate C function declarations for class template methods
     * @param D ClassTemplateSpecializationDecl
     * @param CStruct The created C struct
     * @return Vector of FunctionDecl* for all methods (added to C TU)
     */
    std::vector<clang::FunctionDecl*> monomorphizeClassMethods(
        clang::ClassTemplateSpecializationDecl* D,
        clang::RecordDecl* CStruct
    );

    /**
     * @brief Generate C function AST node for a function template instantiation
     * @param D FunctionDecl (template instantiation)
     * @return FunctionDecl* representing the monomorphized function (added to C TU)
     */
    clang::FunctionDecl* monomorphizeFunction(clang::FunctionDecl* D);

    /**
     * @brief Generate mangled name for template instantiation
     * @param BaseName Base class/function name
     * @param TemplateArgs Template arguments
     * @return Mangled name (e.g., Stack_int, Array_double_20, Container_int_ptr)
     */
    std::string generateMangledName(const std::string& BaseName,
                                   const clang::TemplateArgumentList& TemplateArgs);

    /**
     * @brief Get nested class mappings for current template being monomorphized
     * @return Map from original nested class name to monomorphized name
     *         E.g., "Node" -> "LinkedList_int_Node"
     *
     * Bug #38 FIX: Expose nested class mappings so CppToCVisitor can substitute
     * types in method bodies correctly
     */
    const std::map<std::string, std::string>& getNestedClassMappings() const {
        return nestedClassMappings;
    }

private:
    clang::ASTContext& Context;
    NameMangler& Mangler;
    clang::CNodeBuilder& Builder;

    // BUG FIX (Bug #18): Track nested class mappings for type substitution
    // Maps original nested class name -> monomorphized struct name
    // E.g., "Node" -> "LinkedList_int_Node"
    std::map<std::string, std::string> nestedClassMappings;

    /**
     * @brief Substitute template parameters with actual types in a QualType
     * @param Type Original type (may contain template parameters)
     * @param TemplateArgs Template arguments for substitution
     * @return Type with template parameters substituted
     */
    clang::QualType substituteType(clang::QualType Type,
                                   const clang::TemplateArgumentList& TemplateArgs);

    /**
     * @brief Convert C++ types to C types (Phase 32.2 - Bug Fix)
     * @param Type QualType that may contain C++ CXXRecordDecl
     * @return QualType with CXXRecordDecl replaced by RecordDecl (TTK_Struct)
     *
     * Ensures generated C code uses "struct" keyword instead of "class".
     * Recursively handles pointers, references, and arrays.
     */
    clang::QualType convertToCType(clang::QualType Type);

    /**
     * @brief Create C struct declaration from template class
     * @param D ClassTemplateSpecializationDecl
     * @param MangledName Mangled struct name
     * @return RecordDecl* (C struct AST node)
     */
    clang::RecordDecl* createStruct(clang::ClassTemplateSpecializationDecl* D,
                                   const std::string& MangledName);

    /**
     * @brief Create C function declaration for template method
     * @param Method CXXMethodDecl
     * @param ClassName Mangled class name
     * @param TemplateArgs Template arguments for type substitution
     * @return FunctionDecl* (C function AST node)
     */
    clang::FunctionDecl* createMethodFunction(clang::CXXMethodDecl* Method,
                                             const std::string& ClassName,
                                             const clang::TemplateArgumentList& TemplateArgs);

    /**
     * @brief Convert QualType to valid C identifier component
     * @param Type Clang QualType
     * @return Valid C identifier string (no *, <, >, ::, etc.)
     *
     * Converts types to valid identifier parts for use in mangled names.
     * Pointer types use "_ptr" suffix (e.g., "int*" -> "int_ptr")
     * Reference types use "_ref" suffix (e.g., "int&" -> "int_ref")
     */
    std::string typeToIdentifierString(clang::QualType Type);
};


#endif // TEMPLATE_MONOMORPHIZER_H
