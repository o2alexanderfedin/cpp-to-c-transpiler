/**
 * @file DynamicCastTranslator.cpp
 * @brief Story #85: dynamic_cast Downcast Support Implementation
 *
 * Translates C++ dynamic_cast expressions to runtime cxx_dynamic_cast() calls.
 * Implements safe downcasting with runtime type checking using Itanium ABI.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only translates dynamic_cast expressions
 * - Open/Closed: Extensible for cross-casting without modification
 * - Liskov Substitution: N/A (no inheritance)
 * - Interface Segregation: Clean public API, private implementation details
 * - Dependency Inversion: Depends on Clang AST abstractions, not concrete types
 */

#include "DynamicCastTranslator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include <sstream>

using namespace clang;

/**
 * @brief Constructor
 */
DynamicCastTranslator::DynamicCastTranslator(ASTContext& Context, VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(Analyzer) {}

/**
 * @brief Translate dynamic_cast expression to C cxx_dynamic_cast() call
 *
 * Strategy:
 * 1. Check if null - return empty string
 * 2. Extract source and target types
 * 3. Generate cxx_dynamic_cast() call with type_info pointers
 *
 * @param CastExpr dynamic_cast expression to translate
 * @return C code for cxx_dynamic_cast() call
 */
std::string DynamicCastTranslator::translateDynamicCast(const CXXDynamicCastExpr* CastExpr) {
    if (!CastExpr) {
        return "";
    }

    // Extract source type from operand
    std::string sourceType = getSourceTypeName(CastExpr);

    // Extract target type from cast expression
    std::string targetType = getTargetTypeName(CastExpr);

    if (sourceType.empty() || targetType.empty()) {
        return "";
    }

    // Generate runtime call
    return generateRuntimeCall(CastExpr, sourceType, targetType);
}

/**
 * @brief Get source type name from cast expression
 *
 * Extracts the type of the expression being cast.
 *
 * @param CastExpr dynamic_cast expression
 * @return Source type name
 */
std::string DynamicCastTranslator::getSourceTypeName(const CXXDynamicCastExpr* CastExpr) {
    if (!CastExpr) {
        return "";
    }

    const clang::Expr* SubExpr = CastExpr->getSubExpr();
    if (!SubExpr) {
        return "";
    }

    QualType SourceType = SubExpr->getType();
    return getClassName(SourceType);
}

/**
 * @brief Get target type name from cast expression
 *
 * Extracts the type being cast to.
 *
 * @param CastExpr dynamic_cast expression
 * @return Target type name
 */
std::string DynamicCastTranslator::getTargetTypeName(const CXXDynamicCastExpr* CastExpr) {
    if (!CastExpr) {
        return "";
    }

    QualType TargetType = CastExpr->getType();
    return getClassName(TargetType);
}

/**
 * @brief Extract class name from QualType
 *
 * Handles:
 * - Direct class types: Base
 * - Pointer types: Base*
 * - Reference types: Base&
 * - Const qualified types: const Base*
 *
 * @param Type Type to extract class name from
 * @return Class name string
 */
std::string DynamicCastTranslator::getClassName(QualType Type) {
    if (Type.isNull()) {
        return "";
    }

    // Strip pointers and references
    while (Type->isPointerType() || Type->isReferenceType()) {
        Type = Type->getPointeeType();
    }

    // Strip const/volatile qualifiers
    Type = Type.getUnqualifiedType();

    // Get CXXRecordDecl
    const CXXRecordDecl* Record = Type->getAsCXXRecordDecl();
    if (!Record) {
        return "";
    }

    return Record->getNameAsString();
}

/**
 * @brief Generate cxx_dynamic_cast() function call
 *
 * Generates runtime call in the format:
 * (struct TargetType*)cxx_dynamic_cast(ptr, &__ti_SourceType, &__ti_TargetType, -1)
 *
 * Parameters:
 * - ptr: Pointer being cast (operand expression)
 * - &__ti_SourceType: Source type_info pointer
 * - &__ti_TargetType: Target type_info pointer
 * - -1: Offset parameter (-1 means runtime check required)
 *
 * @param CastExpr Cast expression
 * @param SourceType Source type name
 * @param TargetType Target type name
 * @return C code for function call
 */
std::string DynamicCastTranslator::generateRuntimeCall(const CXXDynamicCastExpr* CastExpr,
                                                        const std::string& SourceType,
                                                        const std::string& TargetType) {
    std::stringstream ss;

    // Cast result to target type
    ss << "(struct " << TargetType << "*)";

    // Call cxx_dynamic_cast
    ss << "cxx_dynamic_cast(";

    // Parameter 1: pointer being cast
    // For now, use placeholder - full implementation would translate the sub-expression
    ss << "/* ptr */";

    // Parameter 2: source type_info
    ss << ", &__ti_" << SourceType;

    // Parameter 3: target type_info
    ss << ", &__ti_" << TargetType;

    // Parameter 4: offset (-1 for runtime check)
    ss << ", -1";

    ss << ")";

    return ss.str();
}
