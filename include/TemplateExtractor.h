/**
 * @file TemplateExtractor.h
 * @brief Story #67: Template Instantiation Extraction from AST
 *
 * Extracts all template instantiations from Clang AST for monomorphization.
 * Handles class templates, function templates, nested templates, and implicit instantiations.
 */

#ifndef TEMPLATE_EXTRACTOR_H
#define TEMPLATE_EXTRACTOR_H

#include "clang/AST/AST.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <vector>
#include <set>
#include <string>

/**
 * @class TemplateExtractor
 * @brief Extracts template instantiations from the AST
 *
 * Visits the AST and collects all ClassTemplateSpecializationDecl and
 * FunctionDecl (template instantiations). Tracks unique instantiations
 * and handles nested templates.
 *
 * Design: Single Responsibility - Only responsible for extracting template instantiations
 */
class TemplateExtractor : public clang::RecursiveASTVisitor<TemplateExtractor> {
public:
    /**
     * @brief Construct extractor with AST context
     * @param Context Clang AST context
     */
    explicit TemplateExtractor(clang::ASTContext& Context);

    /**
     * @brief Extract all template instantiations from translation unit
     * @param TU Translation unit declaration
     */
    void extractTemplateInstantiations(clang::TranslationUnitDecl* TU);

    /**
     * @brief Get all extracted class template instantiations
     * @return Vector of ClassTemplateSpecializationDecl pointers
     */
    std::vector<clang::ClassTemplateSpecializationDecl*> getClassInstantiations() const;

    /**
     * @brief Get all extracted function template instantiations
     * @return Vector of FunctionDecl pointers
     */
    std::vector<clang::FunctionDecl*> getFunctionInstantiations() const;

    // RecursiveASTVisitor interface
    bool VisitClassTemplateDecl(clang::ClassTemplateDecl* D);
    bool VisitClassTemplateSpecializationDecl(clang::ClassTemplateSpecializationDecl* D);
    bool VisitFunctionTemplateDecl(clang::FunctionTemplateDecl* D);
    bool VisitFunctionDecl(clang::FunctionDecl* D);

private:
    clang::ASTContext& Context;

    // Store unique instantiations (avoid duplicates)
    std::vector<clang::ClassTemplateSpecializationDecl*> classInstantiations;
    std::vector<clang::FunctionDecl*> functionInstantiations;

    // Track seen instantiations to avoid duplicates
    std::set<std::string> seenClassInstantiations;
    std::set<std::string> seenFunctionInstantiations;

    /**
     * @brief Generate unique key for class instantiation
     * @param D ClassTemplateSpecializationDecl
     * @return Unique string key
     */
    std::string getClassInstantiationKey(clang::ClassTemplateSpecializationDecl* D);

    /**
     * @brief Generate unique key for function instantiation
     * @param D FunctionDecl
     * @return Unique string key
     */
    std::string getFunctionInstantiationKey(clang::FunctionDecl* D);

    /**
     * @brief Check if function is a template instantiation
     * @param D FunctionDecl
     * @return True if it's a template instantiation
     */
    bool isFunctionTemplateInstantiation(clang::FunctionDecl* D);
};

#endif // TEMPLATE_EXTRACTOR_H
