/**
 * @file TypeAliasAnalyzer.cpp
 * @brief Phase 53: Implementation of TypeAliasAnalyzer
 *
 * Analyzes C++ type aliases and extracts information needed for
 * translation to C typedefs.
 */

#include "handlers/TypeAliasAnalyzer.h"
#include "clang/AST/Type.h"
#include "clang/AST/DeclTemplate.h"

using namespace clang;

namespace cpptoc {

TypeAliasAnalyzer::TypeAliasAnalyzer(ASTContext& Context, CNodeBuilder& Builder)
    : Context(Context), Builder(Builder) {
}

TypeAliasInfo TypeAliasAnalyzer::analyzeTypeAlias(const TypeAliasDecl* TAD) {
    if (!TAD) {
        return TypeAliasInfo{}; // Return empty info for null input
    }

    TypeAliasInfo info;
    info.aliasName = getAliasName(TAD);
    info.underlyingType = extractUnderlyingType(TAD);
    info.isTemplateAlias = isTemplateTypeAlias(TAD);
    info.isPointerType = isPointerType(info.underlyingType);
    info.isFunctionPointer = isFunctionPointerType(info.underlyingType);
    info.hasConstQualifier = hasConstQualifier(info.underlyingType);
    info.hasVolatileQualifier = hasVolatileQualifier(info.underlyingType);

    return info;
}

QualType TypeAliasAnalyzer::extractUnderlyingType(const TypeAliasDecl* TAD) {
    if (!TAD) {
        return QualType();
    }

    // Get the underlying type from the TypeAliasDecl
    QualType underlyingType = TAD->getUnderlyingType();

    // Resolve through alias chain if needed
    return resolveAliasChain(underlyingType);
}

bool TypeAliasAnalyzer::isTemplateTypeAlias(const TypeAliasDecl* TAD) {
    if (!TAD) {
        return false;
    }

    // Check if this TypeAliasDecl is templated by checking its DeclContext
    return TAD->getDescribedAliasTemplate() != nullptr;
}

std::optional<TypeAliasInfo> TypeAliasAnalyzer::analyzeTemplateTypeAlias(
    const TypeAliasTemplateDecl* TATD
) {
    if (!TATD) {
        return std::nullopt;
    }

    // Get the templated TypeAliasDecl
    TypeAliasDecl* TAD = TATD->getTemplatedDecl();
    if (!TAD) {
        return std::nullopt;
    }

    // Analyze the templated alias
    TypeAliasInfo info = analyzeTypeAlias(TAD);
    info.isTemplateAlias = true; // Ensure this is marked as template

    return info;
}

bool TypeAliasAnalyzer::isFunctionPointerType(QualType Type) {
    if (Type.isNull()) {
        return false;
    }

    // Remove qualifiers and get canonical type
    Type = Type.getCanonicalType();

    // Check if it's a pointer type
    if (const auto* PT = Type->getAs<PointerType>()) {
        // Check if pointee is a function type
        QualType PointeeType = PT->getPointeeType();
        return PointeeType->isFunctionType() || PointeeType->isFunctionProtoType();
    }

    return false;
}

bool TypeAliasAnalyzer::isPointerType(QualType Type) {
    if (Type.isNull()) {
        return false;
    }

    // Check if it's a pointer but NOT a function pointer
    if (Type->isPointerType()) {
        return !isFunctionPointerType(Type);
    }

    return false;
}

std::string TypeAliasAnalyzer::getAliasName(const TypeAliasDecl* TAD) {
    if (!TAD) {
        return "";
    }

    // Get simple name (without namespace qualification)
    return TAD->getNameAsString();
}

bool TypeAliasAnalyzer::hasConstQualifier(QualType Type) {
    if (Type.isNull()) {
        return false;
    }

    return Type.isConstQualified();
}

bool TypeAliasAnalyzer::hasVolatileQualifier(QualType Type) {
    if (Type.isNull()) {
        return false;
    }

    return Type.isVolatileQualified();
}

QualType TypeAliasAnalyzer::resolveAliasChain(QualType Type) {
    if (Type.isNull()) {
        return Type;
    }

    // Follow typedef/alias chain to find ultimate type
    const clang::Type* CurType = Type.getTypePtr();
    while (const auto* TDT = dyn_cast<TypedefType>(CurType)) {
        CurType = TDT->desugar().getTypePtr();
    }

    // Also handle elaborated types (like "struct Foo")
    if (const auto* ET = dyn_cast<ElaboratedType>(CurType)) {
        CurType = ET->getNamedType().getTypePtr();
    }

    // Reconstruct QualType with original qualifiers
    QualType Result(CurType, 0);
    Result.addFastQualifiers(Type.getLocalFastQualifiers());

    return Result;
}

} // namespace cpptoc
