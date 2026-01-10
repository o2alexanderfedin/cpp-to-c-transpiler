/**
 * @file VtableInitializer.h
 * @brief Story #171: Vtable Initialization in Constructors
 *
 * Generates vptr initialization code for constructors of polymorphic classes.
 * The vptr must be initialized to point to the class's vtable before any
 * member initialization or base constructor calls.
 */

#ifndef VTABLE_INITIALIZER_H
#define VTABLE_INITIALIZER_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include <vector>
#include <string>

/**
 * @class VtableInitializer
 * @brief Generates vtable pointer initialization for constructors
 *
 * Responsibilities:
 * - Generate vptr initialization statement (this->vptr = &__vtable_ClassName)
 * - Inject vptr init at the beginning of constructor body
 * - Handle inheritance (each class initializes vptr to its own vtable)
 *
 * C++ Semantics:
 * - Vptr initialized BEFORE member initialization
 * - Vptr initialized BEFORE base constructor calls
 * - Each class in hierarchy sets vptr to its own vtable
 *
 * Example:
 * C++: Shape::Shape() : x(0) { }
 * C:   void Shape__ctor(struct Shape *this) {
 *          this->vptr = &__vtable_Shape;  // Vptr init FIRST
 *          this->x = 0;                   // Then members
 *      }
 */
class VtableInitializer {
public:
    /**
     * @brief Construct initializer with AST context and virtual method analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer
     */
    VtableInitializer(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Generate vptr initialization statement
     * @param Record Class being constructed
     * @param ThisParam 'this' parameter of constructor
     * @param targetLoc Source location for generated AST nodes
     * @return Assignment statement (this->vptr = &__vtable_ClassName), or nullptr if not polymorphic
     */
    clang::Stmt* generateVptrInit(const clang::CXXRecordDecl* Record,
                                   clang::ParmVarDecl* ThisParam,
                                   clang::SourceLocation targetLoc);

    /**
     * @brief Inject vptr initialization into constructor statement list
     * @param Record Class being constructed
     * @param ThisParam 'this' parameter of constructor
     * @param stmts Statement list (modified in-place, vptr init prepended)
     * @param targetLoc Source location for generated AST nodes
     * @return true if vptr init was injected, false if not polymorphic
     *
     * Side effects:
     * - If polymorphic, prepends vptr initialization to stmts
     * - If not polymorphic, stmts unchanged
     */
    bool injectVptrInit(const clang::CXXRecordDecl* Record,
                        clang::ParmVarDecl* ThisParam,
                        std::vector<clang::Stmt*>& stmts,
                        clang::SourceLocation targetLoc);

    /**
     * @brief Get vtable variable name for a class
     * @param Record Class to get vtable name for
     * @return Vtable name (e.g., "__vtable_Shape")
     */
    std::string getVtableName(const clang::CXXRecordDecl* Record) const;

private:
    /**
     * @brief Create member access expression: this->vptr
     * @param ThisParam 'this' parameter
     * @param Record Class being constructed
     * @param targetLoc Source location for generated AST nodes
     * @return MemberExpr for this->vptr
     */
    clang::Expr* createVptrAccess(clang::ParmVarDecl* ThisParam,
                                   const clang::CXXRecordDecl* Record,
                                   clang::SourceLocation targetLoc);

    /**
     * @brief Create address-of vtable expression: &__vtable_ClassName
     * @param Record Class to get vtable address for
     * @param targetLoc Source location for generated AST nodes
     * @return UnaryOperator for address-of vtable
     */
    clang::Expr* createVtableAddress(const clang::CXXRecordDecl* Record,
                                       clang::SourceLocation targetLoc);

    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // VTABLE_INITIALIZER_H
