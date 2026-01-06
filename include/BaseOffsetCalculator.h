/**
 * @file BaseOffsetCalculator.h
 * @brief Helper class to calculate base class offsets for this-pointer adjustment thunks
 *
 * Part of Phase 46: Multiple Inheritance
 * Group 2, Task 4: Base Offset Calculator
 *
 * When a C++ class inherits from multiple polymorphic base classes, calling a method
 * through a non-primary base pointer requires this-pointer adjustment. This class
 * calculates the offsets needed for these adjustments.
 *
 * Example:
 * ```cpp
 * class IDrawable { virtual void draw() = 0; };
 * class ISerializable { virtual void serialize() = 0; };
 * class Shape : public IDrawable, public ISerializable { ... };
 * ```
 *
 * Memory layout:
 * ```
 * Shape object:
 * +0:  lpVtbl (IDrawable - primary base)
 * +8:  lpVtbl2 (ISerializable - non-primary base)
 * +16: x, y (member fields)
 * ```
 *
 * When calling serialize() through ISerializable*, the pointer points to offset +8.
 * The thunk must adjust back to offset 0 to get the original Shape*.
 */

#ifndef BASE_OFFSET_CALCULATOR_H
#define BASE_OFFSET_CALCULATOR_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include <cstdint>

/**
 * @class BaseOffsetCalculator
 * @brief Calculates base class offsets for multiple inheritance this-pointer adjustment
 *
 * This class works in conjunction with MultipleInheritanceAnalyzer to provide
 * precise offset calculations needed for thunk generation.
 *
 * Key differences from MultipleInheritanceAnalyzer:
 * - MultipleInheritanceAnalyzer: Identifies which bases are polymorphic
 * - BaseOffsetCalculator: Calculates exact byte offsets for those bases
 *
 * The calculator uses Clang's ASTRecordLayout API to get accurate offsets that
 * match the actual memory layout of the C++ objects.
 */
class BaseOffsetCalculator {
public:
    /**
     * @brief Constructor
     * @param Context Clang AST context for type layout calculations
     */
    explicit BaseOffsetCalculator(clang::ASTContext& Context);

    /**
     * @brief Get offset in bytes for a specific base in derived class
     * @param Derived The derived class
     * @param Base The base class
     * @return Offset in bytes from start of derived object to base subobject
     *
     * Returns 0 if:
     * - Base is the primary base (no adjustment needed)
     * - Base is not actually a base of Derived
     * - Either parameter is null
     *
     * Example:
     * ```cpp
     * class Derived : public Base1, public Base2 { ... };
     * // getBaseOffset(Derived, Base1) returns 0 (primary)
     * // getBaseOffset(Derived, Base2) returns 8 (sizeof(void*))
     * ```
     */
    uint64_t getBaseOffset(
        const clang::CXXRecordDecl* Derived,
        const clang::CXXRecordDecl* Base
    );

    /**
     * @brief Get offset for specific lpVtbl field (lpVtbl2, lpVtbl3, etc.)
     * @param Derived The derived class
     * @param Base The base class
     * @return Offset in bytes to the lpVtbl field for this base
     *
     * This is the same as getBaseOffset() for direct bases, but provides
     * semantic clarity that we're calculating the lpVtbl field offset
     * specifically for thunk generation.
     *
     * Example:
     * ```cpp
     * // For Shape : public IDrawable, public ISerializable
     * // getLpVtblFieldOffset(Shape, ISerializable) returns offset of lpVtbl2
     * // which is sizeof(void*) = 8 bytes
     * ```
     */
    uint64_t getLpVtblFieldOffset(
        const clang::CXXRecordDecl* Derived,
        const clang::CXXRecordDecl* Base
    );

    /**
     * @brief Check if a base is the primary base
     * @param Derived The derived class
     * @param Base The base class to check
     * @return True if Base is the primary base of Derived
     *
     * The primary base is the first polymorphic base class, which uses lpVtbl
     * and has offset 0 (no this-pointer adjustment needed).
     *
     * Returns false if:
     * - Base is not the first polymorphic base
     * - Base is not a base of Derived at all
     * - Either parameter is null
     */
    bool isPrimaryBase(
        const clang::CXXRecordDecl* Derived,
        const clang::CXXRecordDecl* Base
    );

private:
    clang::ASTContext& Context;

    /**
     * @brief Check if a base class is polymorphic (has virtual methods)
     * @param Base The base class to check
     * @return True if base has virtual methods
     */
    bool isPolymorphicBase(const clang::CXXRecordDecl* Base);
};

#endif // BASE_OFFSET_CALCULATOR_H
