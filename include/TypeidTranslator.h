/**
 * @file TypeidTranslator.h
 * @brief Story #84: typeid Operator Translation
 *
 * Translates C++ typeid expressions to type_info retrieval in C.
 * Handles both polymorphic (vtable lookup) and static (direct reference) cases.
 *
 * SOLID Principles:
 * - Single Responsibility: Translates typeid expressions only
 * - Open/Closed: Extensible for new typeid scenarios
 * - Interface Segregation: Clean public API
 * - Dependency Inversion: Depends on Clang AST abstractions
 */

#ifndef TYPEID_TRANSLATOR_H
#define TYPEID_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include "TypeInfoGenerator.h"
#include <string>

/**
 * @class TypeidTranslator
 * @brief Translates C++ typeid operator to C type_info retrieval
 *
 * The typeid operator has two forms:
 * 1. Polymorphic: typeid(*ptr) - retrieves type_info from vtable at runtime
 * 2. Static: typeid(Type) - returns compile-time constant type_info reference
 *
 * C++ Example:
 *   Base* ptr = new Derived();
 *   const std::type_info& ti = typeid(*ptr);  // Polymorphic (runtime)
 *   const std::type_info& ti2 = typeid(Base); // Static (compile-time)
 *
 * C Translation (Polymorphic - lookup from vtable):
 *   struct Base *ptr = ...;
 *   const struct __class_type_info *ti = ptr->vptr->type_info;
 *
 * C Translation (Static - direct reference):
 *   const struct __class_type_info *ti2 = &__ti_Base;
 *
 * Note: The vtable stores type_info pointer at offset -1 (before function pointers).
 */
class TypeidTranslator {
public:
    /**
     * @brief Construct translator with AST context and virtual method analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer for polymorphism detection
     */
    TypeidTranslator(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Translate typeid expression to C type_info retrieval
     * @param Expr typeid expression to translate
     * @return C code for type_info retrieval (polymorphic or static)
     */
    std::string translateTypeid(const clang::CXXTypeidExpr* Expr);

    /**
     * @brief Check if typeid expression is polymorphic (runtime lookup)
     * @param Expr typeid expression to check
     * @return true if polymorphic (requires vtable lookup), false if static
     *
     * Polymorphic conditions:
     * - Expression operand (not type operand)
     * - Operand is a dereference of polymorphic pointer/reference
     * - Underlying type is polymorphic (has virtual functions)
     */
    bool isPolymorphicTypeid(const clang::CXXTypeidExpr* Expr);

private:
    /**
     * @brief Generate polymorphic typeid translation (vtable lookup)
     * @param Expr typeid expression with polymorphic operand
     * @return C code for vtable lookup: ptr->vptr->type_info
     */
    std::string generatePolymorphicTypeid(const clang::CXXTypeidExpr* Expr);

    /**
     * @brief Generate static typeid translation (direct reference)
     * @param Expr typeid expression with type operand
     * @return C code for static reference: &__ti_ClassName
     */
    std::string generateStaticTypeid(const clang::CXXTypeidExpr* Expr);

    /**
     * @brief Get type from typeid expression (handles both type and expr operands)
     * @param Expr typeid expression
     * @return QualType of the type being queried
     */
    clang::QualType getTypeidType(const clang::CXXTypeidExpr* Expr);

    /**
     * @brief Get class name from type
     * @param Type Type to extract class name from
     * @return Class name string, or empty if not a class type
     */
    std::string getClassName(clang::QualType Type);

    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // TYPEID_TRANSLATOR_H
