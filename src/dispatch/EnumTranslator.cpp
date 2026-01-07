/**
 * @file EnumTranslator.cpp
 * @brief Implementation of EnumTranslator dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle enum translation.
 * Translates both scoped and unscoped C++ enums to C enums.
 * Handles name prefixing for scoped enums (EnumName__ConstantName pattern).
 */

#include "dispatch/EnumTranslator.h"
#include "CNodeBuilder.h"
#include "mapping/DeclMapper.h"
#include "SourceLocationMapper.h"
#include "TargetContext.h"
#include "clang/AST/Decl.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void EnumTranslator::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &EnumTranslator::canHandle,
        &EnumTranslator::handleEnum
    );
}

bool EnumTranslator::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Accept only EnumDecl
    return llvm::isa<clang::EnumDecl>(D);
}

void EnumTranslator::handleEnum(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(llvm::isa<clang::EnumDecl>(D) && "Must be EnumDecl");

    const auto* ED = llvm::cast<clang::EnumDecl>(D);

    // Check if already translated (avoid duplicates)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    if (declMapper.hasCreated(ED)) {
        llvm::outs() << "[EnumTranslator] Already translated enum: "
                     << ED->getNameAsString() << " (skipping)\n";
        return;
    }

    // Get target location for this declaration
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, D);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Extract enum properties
    // CRITICAL: Use getName() not getNameAsString()!
    // getNameAsString() returns temporary std::string, StringRef becomes dangling pointer
    llvm::StringRef enumName = ED->getName();
    std::string enumNameStr = enumName.str(); // Create stable string for logging
    clang::IdentifierInfo& enumII = cASTContext.Idents.get(enumName);

    // Determine if scoped (enum class)
    bool isScoped = ED->isScoped();

    // Extract underlying type (if specified)
    clang::QualType underlyingType = extractUnderlyingType(ED);

    // Get integer type for constants (default to int if not specified)
    clang::QualType intType = underlyingType.isNull() ? cASTContext.IntTy : underlyingType;

    llvm::outs() << "[EnumTranslator] Translating enum: " << enumNameStr
                 << (isScoped ? " (scoped)" : " (unscoped)")
                 << "\n";

    // Create C EnumDecl
    // Note: C enums are never scoped, never have fixed underlying types in C99
    clang::EnumDecl* C_Enum = clang::EnumDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &enumII,
        nullptr,  // No previous declaration
        false,    // Not scoped (C doesn't support scoped enums)
        false,    // Not fixed underlying type (C99 doesn't support this)
        true      // Complete definition
    );

    assert(C_Enum && "Failed to create C EnumDecl");

    // Store mapping EARLY (before translating constants to handle references)
    declMapper.setCreated(ED, C_Enum);

    // Start definition
    C_Enum->startDefinition();

    // Translate enum constants
    for (const clang::EnumConstantDecl* ECD : ED->enumerators()) {
        clang::EnumConstantDecl* C_ECD = translateEnumConstant(
            ECD,
            isScoped,
            enumName,
            C_Enum,  // Pass parent enum
            cASTContext
        );

        if (C_ECD) {
            // Add constant to enum
            C_Enum->addDecl(C_ECD);

            // Register mapping for expression translation
            declMapper.setCreated(ECD, C_ECD);

            llvm::outs() << "[EnumTranslator]   Constant: " << ECD->getNameAsString()
                         << " → " << C_ECD->getNameAsString()
                         << " = " << ECD->getInitVal()
                         << "\n";
        }
    }

    // Complete definition
    C_Enum->completeDefinition(intType, intType, 0, 0);

    // Get or create C TranslationUnit for this target file (reuse targetPath from above)
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTU && "Failed to get/create C TranslationUnit");

    // Add C enum to C TranslationUnit
    C_Enum->setDeclContext(cTU);
    cTU->addDecl(C_Enum);

    // Register node location in PathMapper for tracking
    pathMapper.setNodeLocation(C_Enum, targetPath);

    // Debug output for verification
    size_t constantCount = std::distance(ED->enumerator_begin(), ED->enumerator_end());
    llvm::outs() << "[EnumTranslator] Translated enum: " << enumNameStr
                 << " (" << constantCount << " constants)"
                 << " → " << targetPath << "\n";
}

clang::EnumConstantDecl* EnumTranslator::translateEnumConstant(
    const clang::EnumConstantDecl* ECD,
    bool isScoped,
    llvm::StringRef prefix,
    clang::EnumDecl* parentEnum,
    clang::ASTContext& cASTContext
) {
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

    clang::IdentifierInfo& constII = cASTContext.Idents.get(constantName);

    // Get constant value
    llvm::APSInt value = ECD->getInitVal();

    // Get type (use int for C enums)
    clang::QualType type = cASTContext.IntTy;

    // Get target location from parent enum (which was already created with proper location)
    clang::SourceLocation targetLoc = parentEnum->getLocation();

    // Create C EnumConstantDecl with parent enum
    clang::EnumConstantDecl* C_ECD = clang::EnumConstantDecl::Create(
        cASTContext,
        parentEnum,  // Parent EnumDecl must be set at creation time
        targetLoc,
        &constII,
        type,
        nullptr,  // No initializer expression
        value
    );

    assert(C_ECD && "Failed to create C EnumConstantDecl");

    return C_ECD;
}

clang::QualType EnumTranslator::extractUnderlyingType(const clang::EnumDecl* ED) {
    // Get the integer type that underlies the enum
    clang::QualType IntType = ED->getIntegerType();

    // Check if explicitly specified (e.g., enum class X : uint8_t)
    if (ED->isFixed()) {
        // Enum has explicit underlying type
        llvm::outs() << "[EnumTranslator]   Underlying type: " << IntType.getAsString() << "\n";
        return IntType;
    }

    // No explicit underlying type - return empty QualType
    return clang::QualType();
}

std::string EnumTranslator::generatePrefixedName(
    llvm::StringRef enumName,
    llvm::StringRef constantName
) {
    // Pattern: EnumName__ConstantName (double underscore separator)
    // Example: GameState::Menu → GameState__Menu
    return (enumName + "__" + constantName).str();
}

} // namespace cpptoc
