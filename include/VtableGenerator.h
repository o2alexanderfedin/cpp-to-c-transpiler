/**
 * @file VtableGenerator.h
 * @brief Phase 31: COM-Style Vtable Generation
 *
 * Generates vtable struct definitions for polymorphic classes using the COM/DCOM
 * approach with strongly-typed function pointers and explicit static declarations.
 *
 * ## Why COM-Style Pattern?
 *
 * The COM/DCOM approach provides compile-time type safety through explicit
 * static declarations for all virtual methods. This differs from implicit
 * signature approaches in three critical ways:
 *
 * ### 1. COMPILE-TIME VERIFICATION
 * - **Before**: Hope generator produces correct signatures
 * - **After**: Compiler verifies declaration matches implementation matches vtable
 * - **Benefit**: Generator bugs caught at compile time, not runtime
 *
 * ### 2. DEBUGGING EXPERIENCE
 * - **Before**: Stack traces show generic function pointer addresses
 * - **After**: Stack traces show actual function names (Shape_getArea, etc.)
 * - **Benefit**: Easier debugging, better profiler output
 *
 * ### 3. SELF-DOCUMENTATION
 * - **Before**: Must read implementation to know signature
 * - **After**: Declaration at top of file serves as interface documentation
 * - **Benefit**: Code is more maintainable and easier to understand
 *
 * ## Trade-offs
 * - **Code size**: ~20% more lines (static declarations)
 * - **Runtime overhead**: ZERO (identical assembly output)
 * - **Generation time**: ~5% slower (still <1ms per class)
 *
 * ## References
 * - Microsoft COM Interface Design: https://docs.microsoft.com/en-us/windows/win32/com/com-interface-design
 * - Research findings: .planning/phases/31-com-vmt-architecture/31-01-FINDINGS.md
 * - Implementation history: Phase 31-02 (v2.2.0), Phase 31-03 (v2.3.0), Phase 31-04 (v2.4.0)
 *
 * ## Example
 *
 * C++ input:
 * ```cpp
 * class Shape {
 * public:
 *     virtual int getArea() = 0;
 *     virtual ~Shape() {}
 * };
 * ```
 *
 * Generated C output:
 * ```c
 * // COM-style static declarations (Phase 31-02)
 * static void Shape__dtor(struct Shape *this);
 * static int Shape_getArea(struct Shape *this);
 *
 * // Vtable structure
 * struct Shape_vtable {
 *     const struct __class_type_info *type_info;  // RTTI
 *     void (*destructor)(struct Shape *this);
 *     int (*getArea)(struct Shape *this);
 * };
 *
 * // Vtable initialization (compiler verifies type match!)
 * static Shape_vtable Shape_vtbl = {
 *     &Shape_typeinfo,
 *     Shape__dtor,      // Compile error if signature mismatch!
 *     Shape_getArea     // Compile error if signature mismatch!
 * };
 * ```
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
 * @brief Generates C vtable struct definitions with COM-style type safety
 *
 * This class implements the COM/DCOM pattern for vtable generation:
 * 1. Explicit static declarations for all virtual methods
 * 2. Strongly-typed function pointers in vtable struct
 * 3. Compile-time verification of signature correctness
 *
 * ## Vtable Structure (Itanium ABI)
 *
 * Vtable layout follows the Itanium C++ ABI:
 * 1. **type_info pointer** (offset 0 in C, offset -1 in C++)
 * 2. **Virtual base offsets** (for virtual inheritance, Story #90)
 * 3. **Virtual method pointers** (destructor first, then methods in declaration order)
 *
 * ## Method Resolution
 *
 * Uses OverrideResolver (required dependency) for correct override resolution:
 * - Handles single and multiple inheritance
 * - Resolves virtual method overrides correctly
 * - Maintains vtable slot consistency across inheritance hierarchy
 *
 * ## Performance Characteristics (Phase 31-04)
 *
 * - Generation time: <1ms for typical class with 10 methods
 * - Memory usage: <50KB per class
 * - Runtime overhead: ZERO (identical assembly to hand-written C)
 *
 * ## Thread Safety
 *
 * - MethodSignatureHelper uses thread-local caches (safe for parallel translation units)
 * - No shared mutable state in VtableGenerator itself
 *
 * @see MethodSignatureHelper for signature generation details
 * @see OverrideResolver for override resolution logic
 * @see VirtualMethodAnalyzer for polymorphism detection
 */
class VtableGenerator {
public:
    /**
     * @brief Construct generator with AST context, virtual method analyzer, and override resolver
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer for detecting polymorphic classes
     * @param Resolver Override resolver for resolving method implementations (required)
     *
     * Phase 31-04: OverrideResolver is now a required dependency (no longer optional).
     * Legacy fallback code has been removed for cleaner, more maintainable codebase.
     */
    VtableGenerator(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer,
                    OverrideResolver* Resolver);

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
     *
     * Phase 31-04: Simplified to delegate directly to OverrideResolver.
     * Legacy fallback code removed - OverrideResolver is now a required dependency
     * and always provides correct override resolution.
     *
     * @see OverrideResolver::resolveVtableLayout for implementation details
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
