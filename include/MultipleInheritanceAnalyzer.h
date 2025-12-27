/**
 * @file MultipleInheritanceAnalyzer.h
 * @brief Analyzes C++ classes with multiple inheritance to identify base classes and calculate offsets
 *
 * Part of Phase 46: Multiple Inheritance
 * Group 1, Task 1: Base Class Analysis
 */

#ifndef MULTIPLE_INHERITANCE_ANALYZER_H
#define MULTIPLE_INHERITANCE_ANALYZER_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include <vector>
#include <string>

/**
 * @class MultipleInheritanceAnalyzer
 * @brief Analyzes multiple inheritance hierarchies to support COM-style multiple vtable pointers
 *
 * When a C++ class inherits from multiple polymorphic base classes, we need to:
 * 1. Identify which bases are polymorphic (have virtual methods)
 * 2. Determine the primary base (first polymorphic base -> uses lpVtbl)
 * 3. Identify non-primary bases (subsequent polymorphic bases -> use lpVtbl2, lpVtbl3, etc.)
 * 4. Calculate memory offsets for each base subobject
 *
 * Example:
 * ```cpp
 * class IDrawable { virtual void draw() = 0; };
 * class ISerializable { virtual void serialize() = 0; };
 * class Shape : public IDrawable, public ISerializable { ... };
 * ```
 *
 * Analysis results:
 * - Primary base: IDrawable (lpVtbl, offset=0)
 * - Non-primary base: ISerializable (lpVtbl2, offset=sizeof(void*))
 */
class MultipleInheritanceAnalyzer {
public:
    /**
     * @struct BaseInfo
     * @brief Information about a polymorphic base class
     */
    struct BaseInfo {
        const clang::CXXRecordDecl* BaseDecl;  ///< Base class declaration
        bool IsPrimary;                         ///< True if this is the primary base
        unsigned Offset;                        ///< Offset in bytes from start of derived object
        std::string VtblFieldName;              ///< Field name: "lpVtbl", "lpVtbl2", "lpVtbl3", etc.
        unsigned VtblIndex;                     ///< Index: 0 for lpVtbl, 1 for lpVtbl2, etc.
    };

    /**
     * @brief Constructor
     * @param Context Clang AST context for type calculations
     */
    explicit MultipleInheritanceAnalyzer(clang::ASTContext& Context);

    /**
     * @brief Analyze all polymorphic base classes of a derived class
     * @param Record The derived class to analyze
     * @return Vector of BaseInfo for each polymorphic base, in declaration order
     *
     * Returns empty vector if:
     * - Record is null
     * - Record has no bases
     * - Record has no polymorphic bases
     */
    std::vector<BaseInfo> analyzePolymorphicBases(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get the primary base class (first polymorphic base)
     * @param Record The derived class
     * @return Primary base or nullptr if no polymorphic base exists
     *
     * The primary base is the first base class that has virtual methods.
     * It uses lpVtbl and has offset=0 within the derived object.
     */
    const clang::CXXRecordDecl* getPrimaryBase(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get non-primary base classes (polymorphic bases after the first)
     * @param Record The derived class
     * @return Vector of non-primary bases
     *
     * These bases use lpVtbl2, lpVtbl3, etc. and have non-zero offsets.
     */
    std::vector<const clang::CXXRecordDecl*> getNonPrimaryBases(const clang::CXXRecordDecl* Record);

    /**
     * @brief Calculate offset of a base class within derived class
     * @param Derived The derived class
     * @param Base The base class
     * @return Offset in bytes, or 0 if Base is not a base of Derived
     *
     * Uses Clang's ASTRecordLayout to get accurate offset information.
     */
    unsigned calculateBaseOffset(const clang::CXXRecordDecl* Derived,
                                  const clang::CXXRecordDecl* Base);

    /**
     * @brief Check if a class has multiple polymorphic bases
     * @param Record The class to check
     * @return True if class has 2 or more polymorphic base classes
     */
    bool hasMultiplePolymorphicBases(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get vtable field name for a base index
     * @param Index 0 for primary base, 1+ for non-primary bases
     * @return "lpVtbl" for index 0, "lpVtbl2" for index 1, "lpVtbl3" for index 2, etc.
     */
    static std::string getVtblFieldName(unsigned Index);

private:
    clang::ASTContext& Context;

    /**
     * @brief Check if a base class is polymorphic (has virtual methods)
     * @param Base The base class to check
     * @return True if base has virtual methods
     */
    bool isPolymorphicBase(const clang::CXXRecordDecl* Base);
};

#endif // MULTIPLE_INHERITANCE_ANALYZER_H
