/**
 * @file TypedefGenerator.cpp
 * @brief Phase 53: Implementation of TypedefGenerator
 *
 * Generates C typedef declarations from type alias information.
 */

#include "handlers/TypedefGenerator.h"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"

using namespace clang;

namespace cpptoc {

TypedefGenerator::TypedefGenerator(ASTContext& Context, CNodeBuilder& Builder)
    : Context(Context), Builder(Builder) {
}

TypedefDecl* TypedefGenerator::generateTypedef(const TypeAliasInfo& info) {
    if (info.aliasName.empty() || info.underlyingType.isNull()) {
        return nullptr;
    }

    // Check if this is a complex type requiring special handling
    if (isComplexType(info.underlyingType)) {
        return handleComplexType(info);
    }

    // Simple typedef generation
    return generateTypedef(info.aliasName, info.underlyingType);
}

TypedefDecl* TypedefGenerator::generateTypedef(
    const std::string& aliasName,
    QualType underlyingType
) {
    if (aliasName.empty() || underlyingType.isNull()) {
        return nullptr;
    }

    // Get the C translation unit as DeclContext
    DeclContext* DC = Context.getTranslationUnitDecl();

    // Create the typedef declaration
    return createTypedefDecl(aliasName, underlyingType, DC);
}

TypedefDecl* TypedefGenerator::handleComplexType(const TypeAliasInfo& info) {
    if (info.isFunctionPointer) {
        return generateFunctionPointerTypedef(info.aliasName, info.underlyingType);
    }

    // Check for array types
    if (const auto* AT = info.underlyingType->getAsArrayTypeUnsafe()) {
        return generateArrayTypedef(info.aliasName, info.underlyingType);
    }

    // Fall back to simple typedef
    return generateTypedef(info.aliasName, info.underlyingType);
}

TypedefDecl* TypedefGenerator::generateFunctionPointerTypedef(
    const std::string& aliasName,
    QualType funcPtrType
) {
    if (aliasName.empty() || funcPtrType.isNull()) {
        return nullptr;
    }

    // Function pointers are handled the same as regular types in C typedef
    // The type itself already encodes the function pointer syntax
    // typedef void (*Callback)(int, float);
    return generateTypedef(aliasName, funcPtrType);
}

TypedefDecl* TypedefGenerator::generateArrayTypedef(
    const std::string& aliasName,
    QualType arrayType
) {
    if (aliasName.empty() || arrayType.isNull()) {
        return nullptr;
    }

    // Array typedefs are handled the same as regular types
    // The type itself already encodes the array syntax
    // typedef int IntArray[10];
    return generateTypedef(aliasName, arrayType);
}

bool TypedefGenerator::isComplexType(QualType Type) {
    if (Type.isNull()) {
        return false;
    }

    // Check for function pointer
    if (const auto* PT = Type->getAs<PointerType>()) {
        QualType PointeeType = PT->getPointeeType();
        if (PointeeType->isFunctionType() || PointeeType->isFunctionProtoType()) {
            return true;
        }
    }

    // Check for array type
    if (Type->isArrayType()) {
        return true;
    }

    return false;
}

TypedefDecl* TypedefGenerator::createTypedefDecl(
    const std::string& aliasName,
    QualType underlyingType,
    DeclContext* DC
) {
    if (!DC) {
        DC = Context.getTranslationUnitDecl();
    }

    // Create TypeSourceInfo for the underlying type
    TypeSourceInfo* TSI = Context.getTrivialTypeSourceInfo(underlyingType);

    // Create the TypedefDecl
    TypedefDecl* TD = TypedefDecl::Create(
        Context,
        DC,
        SourceLocation(), // Start location (synthetic)
        SourceLocation(), // Id location (synthetic)
        &Context.Idents.get(aliasName),
        TSI
    );

    // Add to translation unit
    DC->addDecl(TD);

    return TD;
}

} // namespace cpptoc
