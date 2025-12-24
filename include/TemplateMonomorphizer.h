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
#include "NameMangler.h"
#include <string>
#include <map>

/**
 * @class TemplateMonomorphizer
 * @brief Generates C code from template instantiations
 *
 * Takes ClassTemplateSpecializationDecl and FunctionDecl (template instantiations)
 * and generates equivalent C code with proper type substitution and name mangling.
 *
 * Design: Single Responsibility - Only responsible for monomorphization
 */
class TemplateMonomorphizer {
public:
    /**
     * @brief Construct monomorphizer with AST context and name mangler
     * @param Context Clang AST context
     * @param Mangler Name mangler for generating unique C identifiers
     */
    TemplateMonomorphizer(clang::ASTContext& Context, NameMangler& Mangler);

    /**
     * @brief Generate C code for a class template instantiation
     * @param D ClassTemplateSpecializationDecl
     * @return Generated C code (struct typedef and method declarations)
     */
    std::string monomorphizeClass(clang::ClassTemplateSpecializationDecl* D);

    /**
     * @brief Generate C code for a function template instantiation
     * @param D FunctionDecl (template instantiation)
     * @return Generated C code (function declaration)
     */
    std::string monomorphizeFunction(clang::FunctionDecl* D);

private:
    clang::ASTContext& Context;
    NameMangler& Mangler;

    /**
     * @brief Substitute template parameters with actual types in a QualType
     * @param Type Original type (may contain template parameters)
     * @param TemplateArgs Template arguments for substitution
     * @return Type with template parameters substituted
     */
    clang::QualType substituteType(clang::QualType Type,
                                   const clang::TemplateArgumentList& TemplateArgs);

    /**
     * @brief Generate struct typedef for class instantiation
     * @param D ClassTemplateSpecializationDecl
     * @param MangledName Mangled struct name
     * @return C struct typedef code
     */
    std::string generateStruct(clang::ClassTemplateSpecializationDecl* D,
                              const std::string& MangledName);

    /**
     * @brief Generate method declaration for class method
     * @param Method CXXMethodDecl
     * @param ClassName Mangled class name
     * @param TemplateArgs Template arguments for type substitution
     * @return C function declaration
     */
    std::string generateMethod(clang::CXXMethodDecl* Method,
                               const std::string& ClassName,
                               const clang::TemplateArgumentList& TemplateArgs);

    /**
     * @brief Convert QualType to C type string
     * @param Type Clang QualType
     * @return C type string
     */
    std::string typeToString(clang::QualType Type);

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

    /**
     * @brief Generate mangled name for template instantiation
     * @param BaseName Template base name
     * @param TemplateArgs Template arguments
     * @return Mangled name (e.g., Stack_int, Array_double_20, Container_int_ptr)
     */
    std::string generateMangledName(const std::string& BaseName,
                                   const clang::TemplateArgumentList& TemplateArgs);
};

#endif // TEMPLATE_MONOMORPHIZER_H
