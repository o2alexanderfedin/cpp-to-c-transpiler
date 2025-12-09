/**
 * @file VirtualDestructorHandler.h
 * @brief Story #174: Virtual Destructor Handling
 *
 * Handles virtual destructors for polymorphic delete and destructor chaining.
 * Ensures virtual destructors are placed first in vtables and properly called
 * through inheritance hierarchies.
 */

#ifndef VIRTUAL_DESTRUCTOR_HANDLER_H
#define VIRTUAL_DESTRUCTOR_HANDLER_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include <string>

/**
 * @class VirtualDestructorHandler
 * @brief Handles virtual destructor detection and vtable placement
 *
 * Responsibilities:
 * - Detect virtual destructors
 * - Ensure destructor is first entry in vtable
 * - Support polymorphic delete (base pointer -> derived destructor)
 * - Handle destructor chaining (derived -> base chain)
 * - Integration with RAII resource cleanup
 *
 * Example:
 * class Base {
 *     virtual ~Base() {}  // Virtual destructor
 * };
 *
 * class Derived : public Base {
 *     ~Derived() override {}  // Implicitly virtual
 * };
 *
 * Base* ptr = new Derived();
 * delete ptr;  // Should call ~Derived() then ~Base()
 *
 * Vtable Layout:
 * struct Base_vtable {
 *     void (*destructor)(struct Base *this);  // First entry
 *     // ... other virtual methods
 * };
 */
class VirtualDestructorHandler {
public:
    /**
     * @brief Construct handler with AST context and analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer
     */
    VirtualDestructorHandler(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Check if a destructor is virtual
     * @param Destructor Destructor to check
     * @return true if destructor is virtual (explicit or inherited)
     */
    bool isVirtualDestructor(const clang::CXXDestructorDecl* Destructor) const;

    /**
     * @brief Check if a class has a virtual destructor
     *
     * Returns true if the class declares or inherits a virtual destructor.
     * This includes implicit destructors that are virtual due to base class.
     *
     * @param Record Class to check
     * @return true if class has virtual destructor
     */
    bool hasVirtualDestructor(const clang::CXXRecordDecl* Record) const;

    /**
     * @brief Get vtable name for destructor
     *
     * Returns standard name "destructor" for vtable function pointer.
     *
     * @param Destructor Destructor method
     * @return "destructor" for vtable entry
     */
    std::string getDestructorVtableName(const clang::CXXDestructorDecl* Destructor) const;

    /**
     * @brief Check if destructor should be first in vtable
     *
     * Per C++ ABI, destructors should be placed before other virtual methods
     * in the vtable to ensure proper polymorphic delete.
     *
     * @param Record Class to check
     * @return true if destructor should be first vtable entry
     */
    bool shouldDestructorBeFirstInVtable(const clang::CXXRecordDecl* Record) const;

private:
    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // VIRTUAL_DESTRUCTOR_HANDLER_H
