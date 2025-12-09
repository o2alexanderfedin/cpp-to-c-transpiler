/**
 * @file VirtualMethodAnalyzer.h
 * @brief Story #167: Virtual Method Detection and AST Analysis
 *
 * Provides analysis of virtual methods, polymorphic classes, and abstract classes.
 * This component detects virtual methods (including inherited ones), identifies
 * pure virtual methods, and determines if a class is abstract.
 */

#ifndef VIRTUAL_METHOD_ANALYZER_H
#define VIRTUAL_METHOD_ANALYZER_H

#include "clang/AST/AST.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <vector>

/**
 * @class VirtualMethodAnalyzer
 * @brief Analyzes classes for virtual methods and polymorphic behavior
 *
 * Provides utilities to:
 * - Detect polymorphic classes (classes with virtual methods)
 * - Extract all virtual methods from a class (including inherited)
 * - Identify pure virtual methods
 * - Determine if a class is abstract
 */
class VirtualMethodAnalyzer {
public:
    /**
     * @brief Construct analyzer with AST context
     * @param Context Clang AST context
     */
    explicit VirtualMethodAnalyzer(clang::ASTContext& Context);

    /**
     * @brief Check if a class is polymorphic (has virtual methods)
     * @param Record Class to check
     * @return true if class has at least one virtual method
     */
    bool isPolymorphic(const clang::CXXRecordDecl* Record) const;

    /**
     * @brief Get all virtual methods from a class (including inherited)
     * @param Record Class to analyze
     * @return Vector of virtual method declarations
     */
    std::vector<clang::CXXMethodDecl*> getVirtualMethods(const clang::CXXRecordDecl* Record) const;

    /**
     * @brief Check if a method is pure virtual (= 0)
     * @param Method Method to check
     * @return true if method is pure virtual
     */
    bool isPureVirtual(const clang::CXXMethodDecl* Method) const;

    /**
     * @brief Check if a class is abstract (has at least one pure virtual method)
     * @param Record Class to check
     * @return true if class is abstract
     */
    bool isAbstractClass(const clang::CXXRecordDecl* Record) const;

private:
    clang::ASTContext& Context;
};

#endif // VIRTUAL_METHOD_ANALYZER_H
