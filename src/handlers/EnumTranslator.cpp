/**
 * @file EnumTranslator.cpp
 * @brief Implementation of EnumTranslator (Phase 47)
 *
 * Translates C++ enum declarations to C-compatible enums with:
 * - Scoped enum → unscoped with prefixed constants
 * - Type specifications handled via typedef (C99 approach)
 * - Enum constant mappings registered for expression translation
 */

#include "handlers/EnumTranslator.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/Decl.h"
#include "llvm/ADT/APSInt.h"

namespace cpptoc {

bool EnumTranslator::canHandle(const clang::Decl* D) const {
    return llvm::isa<clang::EnumDecl>(D);
}

clang::Decl* EnumTranslator::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    const clang::EnumDecl* ED = llvm::cast<clang::EnumDecl>(D);

    // Get C AST context and builder
    clang::ASTContext& C_Ctx = ctx.getCContext();
    clang::CNodeBuilder& builder = ctx.getBuilder();

    // Get enum name
    // CRITICAL: Use getName() not getNameAsString()!
    // getNameAsString() returns temporary std::string, StringRef becomes dangling pointer
    llvm::StringRef enumName = ED->getName();
    clang::IdentifierInfo& enumII = C_Ctx.Idents.get(enumName);

    // Determine if scoped (enum class)
    bool isScoped = ED->isScoped();

    // Extract underlying type (if specified)
    clang::QualType underlyingType = extractUnderlyingType(ED);

    // Get integer type for constants (default to int if not specified)
    clang::QualType intType = underlyingType.isNull() ? C_Ctx.IntTy : underlyingType;

    // Create C EnumDecl
    // Note: C enums are never scoped, never have fixed underlying types in C99
    clang::EnumDecl* C_Enum = clang::EnumDecl::Create(
        C_Ctx,
        C_Ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &enumII,
        nullptr,  // No previous declaration
        false,    // Not scoped (C doesn't support scoped enums)
        false,    // Not fixed underlying type (C99 doesn't support this)
        true      // Complete definition
    );

    // Start definition
    C_Enum->startDefinition();

    // Translate enum constants
    for (const clang::EnumConstantDecl* ECD : ED->enumerators()) {
        clang::EnumConstantDecl* C_ECD = translateEnumConstant(
            ECD,
            isScoped,
            enumName,
            C_Enum,  // Pass parent enum
            ctx
        );

        if (C_ECD) {
            // Add constant to enum
            C_Enum->addDecl(C_ECD);

            // Register mapping for expression translation
            ctx.registerDecl(ECD, C_ECD);
        }
    }

    // Complete definition
    C_Enum->completeDefinition(intType, intType, 0, 0);

    // Add to translation unit
    C_Ctx.getTranslationUnitDecl()->addDecl(C_Enum);

    // Register enum mapping
    ctx.registerDecl(ED, C_Enum);

    // Generate typedef if needed (type-specified enums use typedef in C99)
    if (!underlyingType.isNull()) {
        generateTypedef(C_Enum, underlyingType, ctx);
    }

    return C_Enum;
}

clang::EnumConstantDecl* EnumTranslator::translateEnumConstant(
    const clang::EnumConstantDecl* ECD,
    bool isScoped,
    llvm::StringRef prefix,
    clang::EnumDecl* parentEnum,
    HandlerContext& ctx
) {
    clang::ASTContext& C_Ctx = ctx.getCContext();

    // Get constant name
    // CRITICAL: Use getName() not getNameAsString()!
    // getNameAsString() returns temporary std::string, StringRef becomes dangling pointer
    // getName() returns StringRef to stable IdentifierInfo storage
    llvm::StringRef originalName = ECD->getName();

    // Apply prefixing for scoped enums
    std::string constantName;
    if (isScoped) {
        constantName = generatePrefixedName(prefix, originalName);
    } else {
        constantName = originalName.str();
    }

    clang::IdentifierInfo& constII = C_Ctx.Idents.get(constantName);

    // Get constant value
    llvm::APSInt value = ECD->getInitVal();

    // Get type (use int for C enums)
    clang::QualType type = C_Ctx.IntTy;

    // Create C EnumConstantDecl with parent enum
    clang::EnumConstantDecl* C_ECD = clang::EnumConstantDecl::Create(
        C_Ctx,
        parentEnum,  // Parent EnumDecl must be set at creation time
        clang::SourceLocation(),
        &constII,
        type,
        nullptr,  // No initializer expression
        value
    );

    return C_ECD;
}

clang::QualType EnumTranslator::extractUnderlyingType(const clang::EnumDecl* ED) {
    // Get the integer type that underlies the enum
    clang::QualType IntType = ED->getIntegerType();

    // Check if explicitly specified (e.g., enum class X : uint8_t)
    if (ED->isFixed()) {
        // Enum has explicit underlying type
        return IntType;
    }

    // No explicit underlying type - return empty QualType
    return clang::QualType();
}

void EnumTranslator::generateTypedef(
    const clang::EnumDecl* C_Enum,
    clang::QualType underlyingType,
    HandlerContext& ctx
) {
    // NOTE: This method is intentionally a no-op for now.
    //
    // Reason: C99 typedef syntax (typedef enum { ... } Name;) is handled
    // by CodeGenerator during code emission, not during AST construction.
    //
    // The CodeGenerator already checks EnumDecl::isFixed() and generates
    // typedef automatically for type-specified enums.
    //
    // Future enhancement: If we want to represent typedef in C AST,
    // we would create a TypedefDecl here:
    //
    //   clang::ASTContext& C_Ctx = ctx.getCContext();
    //   clang::IdentifierInfo& II = C_Ctx.Idents.get(C_Enum->getNameAsString());
    //   clang::QualType enumType = C_Ctx.getEnumType(C_Enum);
    //
    //   clang::TypedefDecl* TD = clang::TypedefDecl::Create(
    //       C_Ctx,
    //       C_Ctx.getTranslationUnitDecl(),
    //       clang::SourceLocation(),
    //       clang::SourceLocation(),
    //       &II,
    //       C_Ctx.getTrivialTypeSourceInfo(enumType)
    //   );
    //
    //   C_Ctx.getTranslationUnitDecl()->addDecl(TD);
    //
    // However, this is not necessary for current implementation since
    // CodeGenerator handles typedef emission correctly.

    (void)C_Enum;         // Unused in current implementation
    (void)underlyingType;  // Unused in current implementation
    (void)ctx;            // Unused in current implementation
}

std::string EnumTranslator::generatePrefixedName(
    llvm::StringRef enumName,
    llvm::StringRef constantName
) {
    // Pattern: EnumName__ConstantName
    // Example: GameState::Menu → GameState__Menu
    return (enumName + "__" + constantName).str();
}

} // namespace cpptoc
