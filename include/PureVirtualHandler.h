/**
 * @file PureVirtualHandler.h
 * @brief Story #173: Pure Virtual Function Support
 *
 * Handles detection and processing of pure virtual functions and abstract classes.
 * Prevents instantiation of abstract classes and ensures proper vtable handling.
 */

#ifndef PURE_VIRTUAL_HANDLER_H
#define PURE_VIRTUAL_HANDLER_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include <vector>

/**
 * @class PureVirtualHandler
 * @brief Handles pure virtual functions and abstract classes
 *
 * Responsibilities:
 * - Detect pure virtual methods (= 0)
 * - Identify abstract classes (classes with at least one unimplemented pure virtual)
 * - Provide list of pure virtual methods for a class
 * - Ensure no vtable instance is generated for abstract classes
 *
 * Example:
 * class Abstract {
 *     virtual void method() = 0;  // Pure virtual
 * };
 *
 * class Concrete : public Abstract {
 *     void method() override {}   // Implements pure virtual
 * };
 */
class PureVirtualHandler {
public:
    /**
     * @brief Construct handler with AST context and analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer
     */
    PureVirtualHandler(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Check if a method is pure virtual
     * @param Method Method to check
     * @return true if method is pure virtual (= 0)
     */
    bool isPureVirtual(const clang::CXXMethodDecl* Method) const;

    /**
     * @brief Check if a class is abstract
     *
     * A class is abstract if it has at least one pure virtual method
     * that is not overridden by a concrete implementation.
     *
     * @param Record Class to check
     * @return true if class is abstract (cannot be instantiated)
     */
    bool isAbstractClass(const clang::CXXRecordDecl* Record) const;

    /**
     * @brief Get all pure virtual methods of a class
     *
     * Returns methods declared as pure virtual in this class,
     * not including inherited pure virtuals.
     *
     * @param Record Class to analyze
     * @return Vector of pure virtual methods
     */
    std::vector<clang::CXXMethodDecl*> getPureVirtualMethods(
        const clang::CXXRecordDecl* Record) const;

private:
    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // PURE_VIRTUAL_HANDLER_H
