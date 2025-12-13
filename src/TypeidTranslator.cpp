/**
 * @file TypeidTranslator.cpp
 * @brief Story #84: typeid Operator Translation Implementation
 *
 * Translates C++ typeid expressions to type_info retrieval in C.
 * Implements polymorphic (vtable lookup) and static (direct reference) translation.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only translates typeid expressions
 * - Open/Closed: Extensible for new typeid scenarios without modification
 * - Liskov Substitution: N/A (no inheritance hierarchy)
 * - Interface Segregation: Clean public API, private implementation details
 * - Dependency Inversion: Depends on Clang AST abstractions, not concrete types
 */

#include "TypeidTranslator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include <sstream>

using namespace clang;

/**
 * @brief Constructor
 */
TypeidTranslator::TypeidTranslator(ASTContext& Context, VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(Analyzer) {}

/**
 * @brief Translate typeid expression to C type_info retrieval
 *
 * Strategy:
 * 1. Check if null - return empty string
 * 2. Determine if polymorphic or static
 * 3. Generate appropriate translation
 *
 * @param Expr typeid expression to translate
 * @return C code for type_info retrieval
 */
std::string TypeidTranslator::translateTypeid(const CXXTypeidExpr* TypeidExpr) {
    if (!TypeidExpr) {
        return "";
    }

    // Determine translation type
    if (isPolymorphicTypeid(TypeidExpr)) {
        return generatePolymorphicTypeid(TypeidExpr);
    } else {
        return generateStaticTypeid(TypeidExpr);
    }
}

/**
 * @brief Check if typeid expression is polymorphic
 *
 * Polymorphic typeid conditions (Itanium ABI):
 * 1. Expression operand (not type operand): typeid(*ptr) vs typeid(Type)
 * 2. Operand must be a glvalue of polymorphic class type
 * 3. NOT a null pointer constant
 *
 * @param Expr typeid expression to check
 * @return true if requires runtime lookup, false if compile-time constant
 */
bool TypeidTranslator::isPolymorphicTypeid(const CXXTypeidExpr* TypeidExpr) {
    if (!TypeidExpr) {
        return false;
    }

    // Type operand: typeid(Type) - always static
    if (TypeidExpr->isTypeOperand()) {
        return false;
    }

    // Expression operand: typeid(expr)
    // Check if expression type is polymorphic
    const clang::Expr* Operand = TypeidExpr->getExprOperand();
    if (!Operand) {
        return false;
    }

    QualType OperandType = Operand->getType();

    // Strip references and pointers to get underlying type
    if (OperandType->isReferenceType()) {
        OperandType = OperandType->getPointeeType();
    }
    if (OperandType->isPointerType()) {
        OperandType = OperandType->getPointeeType();
    }

    // Get CXXRecordDecl
    const CXXRecordDecl* Record = OperandType->getAsCXXRecordDecl();
    if (!Record) {
        return false;
    }

    // Check if polymorphic using analyzer
    return Analyzer.isPolymorphic(Record);
}

/**
 * @brief Generate polymorphic typeid translation (vtable lookup)
 *
 * Itanium ABI: type_info pointer stored at vtable[-1] (offset -1)
 *
 * Translation pattern:
 * C++: const std::type_info& ti = typeid(*ptr);
 * C:   const struct __class_type_info *ti = ptr->vptr->type_info;
 *
 * Alternative (direct offset access):
 * C:   const struct __class_type_info *ti = ((const struct __class_type_info**)ptr->vptr)[-1];
 *
 * For now, we use simpler approach assuming vptr struct has type_info field at offset -1.
 *
 * @param Expr typeid expression with polymorphic operand
 * @return C code for vtable lookup
 */
std::string TypeidTranslator::generatePolymorphicTypeid(const CXXTypeidExpr* TypeidExpr) {
    if (!TypeidExpr || TypeidExpr->isTypeOperand()) {
        return "";
    }

    const clang::Expr* Operand = TypeidExpr->getExprOperand();
    if (!Operand) {
        return "";
    }

    std::stringstream ss;

    // For simplicity, assume operand is *ptr and generate ptr->vptr->type_info
    // In full implementation, would need to handle the operand properly

    // Get type for casting
    QualType Type = getTypeidType(TypeidExpr);
    std::string className = getClassName(Type);

    // Generate: ((const struct __class_type_info**)ptr->vptr)[-1]
    // This accesses type_info at offset -1 in vtable
    // Note: In actual implementation, we'd need to properly translate the operand expression
    ss << "((const struct __class_type_info**)";
    ss << "/* ptr */";  // Placeholder - would be actual operand translation
    ss << "->vptr)[-1]";

    return ss.str();
}

/**
 * @brief Generate static typeid translation (direct reference)
 *
 * Translation pattern:
 * C++: const std::type_info& ti = typeid(Base);
 * C:   const struct __class_type_info *ti = &__ti_Base;
 *
 * @param Expr typeid expression with type operand
 * @return C code for static reference
 */
std::string TypeidTranslator::generateStaticTypeid(const CXXTypeidExpr* TypeidExpr) {
    if (!TypeidExpr) {
        return "";
    }

    QualType Type = getTypeidType(TypeidExpr);
    std::string className = getClassName(Type);

    if (className.empty()) {
        return "";
    }

    std::stringstream ss;
    ss << "&__ti_" << className;
    return ss.str();
}

/**
 * @brief Get type from typeid expression
 *
 * Handles both:
 * - Type operand: typeid(Base) -> Base
 * - Expression operand: typeid(*ptr) -> Base (underlying type)
 *
 * @param Expr typeid expression
 * @return QualType of the type being queried
 */
QualType TypeidTranslator::getTypeidType(const CXXTypeidExpr* TypeidExpr) {
    if (!TypeidExpr) {
        return QualType();
    }

    if (TypeidExpr->isTypeOperand()) {
        // Type operand: typeid(Type)
        return TypeidExpr->getTypeOperand(Context);
    } else {
        // Expression operand: typeid(expr)
        const clang::Expr* Operand = TypeidExpr->getExprOperand();
        if (!Operand) {
            return QualType();
        }

        QualType Type = Operand->getType();

        // Strip references
        if (Type->isReferenceType()) {
            Type = Type->getPointeeType();
        }

        // For polymorphic types, this is the static type
        // (actual runtime type comes from vtable)
        return Type;
    }
}

/**
 * @brief Get class name from type
 *
 * Handles:
 * - Direct class types: Base
 * - Pointer types: Base*
 * - Reference types: Base&
 *
 * @param Type Type to extract class name from
 * @return Class name string
 */
std::string TypeidTranslator::getClassName(QualType Type) {
    if (Type.isNull()) {
        return "";
    }

    // Strip pointers and references
    while (Type->isPointerType() || Type->isReferenceType()) {
        Type = Type->getPointeeType();
    }

    // Get CXXRecordDecl
    const CXXRecordDecl* Record = Type->getAsCXXRecordDecl();
    if (!Record) {
        return "";
    }

    return Record->getNameAsString();
}
