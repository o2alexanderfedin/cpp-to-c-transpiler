/**
 * @file ConstructorSplitter.h
 * @brief Story #92: Constructor Splitting (C1/C2 Variants)
 *
 * Splits constructors into C1 (complete object) and C2 (base object) variants
 * for classes with virtual inheritance, following Itanium C++ ABI.
 */

#ifndef CONSTRUCTOR_SPLITTER_H
#define CONSTRUCTOR_SPLITTER_H

#include "clang/AST/AST.h"
#include <string>

// Forward declarations
class VirtualInheritanceAnalyzer;

/**
 * @class ConstructorSplitter
 * @brief Generates C1 and C2 constructor variants for virtual inheritance
 *
 * Itanium ABI Constructor Variants:
 * - C1 (Complete Object): Constructs virtual bases, calls base C2 constructors
 * - C2 (Base Object): Skips virtual bases, used when constructing as base class
 *
 * Example output:
 * void Diamond_C1(struct Diamond *this, const void **vtt) {
 *     // Construct virtual base Base
 *     Base_C1((struct Base*)((char*)this + offset));
 *
 *     // Call base C2 constructors
 *     Left_C2((struct Left*)this, vtt[1]);
 *     Right_C2((struct Right*)this, vtt[2]);
 *
 *     // Initialize own members
 *     this->d = 0;
 *
 *     // Set vtables from VTT
 *     this->vptr = vtt[0];
 * }
 */
class ConstructorSplitter {
public:
    /**
     * @brief Construct splitter with AST context and virtual inheritance analyzer
     * @param Context Clang AST context
     * @param ViAnalyzer Virtual inheritance analyzer
     */
    ConstructorSplitter(clang::ASTContext& Context,
                        const VirtualInheritanceAnalyzer& ViAnalyzer);

    /**
     * @brief Check if class needs C1/C2 constructor splitting
     * @param Record Class to check
     * @return true if class has virtual bases and needs splitting
     */
    bool needsSplitting(const clang::CXXRecordDecl* Record) const;

    /**
     * @brief Generate C1 (complete object) constructor
     * @param Record Class to generate constructor for
     * @return C code for C1 constructor
     */
    std::string generateC1Constructor(const clang::CXXRecordDecl* Record);

    /**
     * @brief Generate C2 (base object) constructor
     * @param Record Class to generate constructor for
     * @return C code for C2 constructor
     */
    std::string generateC2Constructor(const clang::CXXRecordDecl* Record);

private:
    /**
     * @brief Generate virtual base construction code (C1 only)
     * @param Record Class being constructed
     * @return C code for constructing virtual bases
     */
    std::string generateVirtualBaseConstruction(const clang::CXXRecordDecl* Record);

    /**
     * @brief Generate base class constructor calls
     * @param Record Class being constructed
     * @param useC2 If true, call C2 constructors; otherwise call C1
     * @return C code for base constructor calls
     */
    std::string generateBaseConstructorCalls(const clang::CXXRecordDecl* Record, bool useC2);

    /**
     * @brief Generate member initialization code
     * @param Record Class being constructed
     * @return C code for initializing own members
     */
    std::string generateMemberInitialization(const clang::CXXRecordDecl* Record);

    /**
     * @brief Generate vtable pointer assignment from VTT
     * @param Record Class being constructed
     * @return C code for setting vtable pointers
     */
    std::string generateVtableAssignment(const clang::CXXRecordDecl* Record);

    /**
     * @brief Get constructor name (C1 or C2 variant)
     * @param Record Class
     * @param isC1 true for C1, false for C2
     * @return Constructor function name
     */
    std::string getConstructorName(const clang::CXXRecordDecl* Record, bool isC1) const;

    clang::ASTContext& Context;
    const VirtualInheritanceAnalyzer& ViAnalyzer;
};

#endif // CONSTRUCTOR_SPLITTER_H
