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
#include <cstddef>

// Forward declarations
class OverrideResolver;
class VirtualInheritanceAnalyzer;

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
     * @brief Construct generator with AST context, virtual method analyzer, and override resolver
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer for detecting polymorphic classes
     * @param Resolver Override resolver for resolving method implementations (optional, can be null for legacy behavior)
     */
    VtableGenerator(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer,
                    OverrideResolver* Resolver = nullptr);

    /**
     * @brief Generate vtable struct definition for a polymorphic class
     * @param Record Class to generate vtable for
     * @return C code for vtable struct, or empty string if not polymorphic
     */
    std::string generateVtableStruct(const clang::CXXRecordDecl* Record);

    /**
     * @brief Generate COM-style static declarations for virtual methods
     * @param Record Class to generate declarations for
     * @return C code for static function declarations, or empty string if not polymorphic
     *
     * Generates static function declarations for all virtual methods in a class.
     * This provides compile-time type safety by ensuring function signatures match
     * vtable function pointer types exactly.
     *
     * Example output:
     *   // Static declarations for Shape virtual methods
     *   static void Shape__dtor(struct Shape *this);
     *   static int Shape_getArea(struct Shape *this);
     *   static void Shape_draw(struct Shape *this);
     */
    std::string generateStaticDeclarations(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get ordered list of methods for vtable
     * @param Record Class to analyze
     * @return Vector of methods in vtable order (destructor first, then virtual methods)
     */
    std::vector<clang::CXXMethodDecl*> getVtableMethodOrder(const clang::CXXRecordDecl* Record);

    /**
     * @brief Generate vtable struct with virtual base offset tables
     * @param Record Class to generate vtable for
     * @param ViAnalyzer Virtual inheritance analyzer with virtual base information
     * @return C code for vtable struct with virtual base offsets, or empty string if not polymorphic
     */
    std::string generateVtableWithVirtualBaseOffsets(const clang::CXXRecordDecl* Record,
                                                      const class VirtualInheritanceAnalyzer& ViAnalyzer);

    /**
     * @brief Calculate offset from derived class to virtual base
     * @param Derived Derived class
     * @param VirtualBase Virtual base class
     * @param Context AST context for type information
     * @return Offset in bytes from derived to virtual base
     */
    ptrdiff_t calculateVirtualBaseOffset(const clang::CXXRecordDecl* Derived,
                                          const clang::CXXRecordDecl* VirtualBase,
                                          clang::ASTContext& Context);

    /**
     * @brief Generate helper function to access virtual base pointer
     * @param Derived Derived class
     * @param VirtualBase Virtual base class
     * @return C code for virtual base access helper function
     */
    std::string generateVirtualBaseAccessHelper(const clang::CXXRecordDecl* Derived,
                                                 const clang::CXXRecordDecl* VirtualBase);

private:
    /**
     * @brief Generate function pointer declaration for a method
     * @param Method Method to generate pointer for
     * @param ClassName Name of the class (for 'this' parameter)
     * @return C function pointer declaration
     */
    std::string generateFunctionPointer(const clang::CXXMethodDecl* Method, const std::string& ClassName);

    /**
     * @brief Generate static function signature for a method
     * @param Method Method to generate signature for
     * @param ClassName Name of the class (for 'this' parameter and function naming)
     * @return C function signature (e.g., "static int ClassName_methodName(struct ClassName *this, int param)")
     */
    std::string getMethodSignature(const clang::CXXMethodDecl* Method, const std::string& ClassName);

    /**
     * @brief Get C type string from Clang QualType
     * @param Type Clang type
     * @return C type string
     */
    std::string getTypeString(clang::QualType Type);

    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
    OverrideResolver* Resolver;  // Story #170: Override resolution
};

#endif // VTABLE_GENERATOR_H
