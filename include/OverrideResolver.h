/**
 * @file OverrideResolver.h
 * @brief Story #170: Virtual Function Override Resolution
 *
 * Resolves which implementation of a virtual method should be used in a vtable.
 * Handles method overriding, inheritance, and maintains vtable slot consistency
 * across inheritance hierarchies.
 */

#ifndef OVERRIDE_RESOLVER_H
#define OVERRIDE_RESOLVER_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include <vector>
#include <map>
#include <string>

/**
 * @class OverrideResolver
 * @brief Resolves virtual method overrides and builds vtable layouts
 *
 * Responsibilities:
 * - Track virtual methods through inheritance hierarchy
 * - Identify which methods override base methods
 * - Build complete vtable layout with correct method implementations
 * - Maintain slot consistency (same order in base and derived vtables)
 *
 * Algorithm:
 * 1. Walk inheritance hierarchy from base to derived
 * 2. Track method signatures to detect overrides
 * 3. Build vtable slots maintaining declaration order
 * 4. Replace base implementations with derived overrides
 *
 * Example:
 * class Base { virtual void foo(); virtual void bar(); };
 * class Derived : public Base { void foo() override; };
 *
 * Base vtable:    [destructor, foo(Base), bar(Base)]
 * Derived vtable: [destructor, foo(Derived), bar(Base)]
 *                                    ^^^^^^^ override  ^^^^^^^ inherited
 */
class OverrideResolver {
public:
    /**
     * @brief Construct resolver with AST context and virtual method analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer
     */
    OverrideResolver(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Resolve complete vtable layout for a class
     * @param Record Class to resolve vtable for
     * @return Ordered vector of methods in vtable (with overrides resolved)
     *
     * Returns methods in vtable order:
     * 1. Destructor (if present)
     * 2. Virtual methods in declaration order (base methods first)
     *
     * For overridden methods, returns the most derived implementation.
     */
    std::vector<clang::CXXMethodDecl*> resolveVtableLayout(const clang::CXXRecordDecl* Record);

    /**
     * @brief Check if a method overrides a base class method
     * @param Method Method to check
     * @param BaseMethod Potential base method
     * @return true if Method overrides BaseMethod
     */
    bool isOverride(const clang::CXXMethodDecl* Method,
                    const clang::CXXMethodDecl* BaseMethod) const;

    /**
     * @brief Get method signature for override matching
     * @param Method Method to get signature for
     * @return Signature string (name + parameter types)
     */
    std::string getMethodSignature(const clang::CXXMethodDecl* Method) const;

private:
    /**
     * @struct VtableSlot
     * @brief Represents a slot in the vtable
     */
    struct VtableSlot {
        std::string signature;           // Method signature for matching
        clang::CXXMethodDecl* method;   // Current method implementation
        unsigned slotIndex;              // Position in vtable
    };

    /**
     * @brief Collect all virtual methods from class hierarchy
     * @param Record Class to collect from
     * @param slots Map of signature -> vtable slot
     * @param slotIndex Current slot index (for ordering)
     */
    void collectVirtualMethods(const clang::CXXRecordDecl* Record,
                               std::map<std::string, VtableSlot>& slots,
                               unsigned& slotIndex);

    /**
     * @brief Get parameter type string for signature matching
     * @param Type Parameter type
     * @return Type string
     */
    std::string getTypeSignature(clang::QualType Type) const;

    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // OVERRIDE_RESOLVER_H
