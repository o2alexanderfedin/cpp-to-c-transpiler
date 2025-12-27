/**
 * @file StaticMemberTranslator.cpp
 * @brief Implementation of StaticMemberTranslator class (Phase 49)
 *
 * Translates C++ static data members to C global variables with mangled names.
 */

#include "helpers/StaticMemberTranslator.h"
#include "NameMangler.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include <vector>

using namespace clang;

namespace cpptoc {

// ============================================================================
// Detection
// ============================================================================

std::vector<VarDecl*> StaticMemberTranslator::detectStaticMembers(
    const CXXRecordDecl* record
) {
    std::vector<VarDecl*> staticMembers;

    if (!record) {
        return staticMembers;
    }

    // Walk through all declarations in the class
    // Note: fields() only returns non-static fields, we need decls()
    for (auto* decl : record->decls()) {
        // Check if it's a VarDecl (variable declaration)
        if (auto* varDecl = dyn_cast<VarDecl>(decl)) {
            // Check if it's a static data member
            if (varDecl->isStaticDataMember()) {
                staticMembers.push_back(varDecl);
            }
        }
    }

    return staticMembers;
}

// ============================================================================
// Declaration Generation (for header)
// ============================================================================

VarDecl* StaticMemberTranslator::generateStaticDeclaration(
    VarDecl* staticMember,
    HandlerContext& ctx
) {
    if (!staticMember || !staticMember->isStaticDataMember()) {
        return nullptr;
    }

    // Get the owning class
    auto* record = dyn_cast<CXXRecordDecl>(staticMember->getDeclContext());
    if (!record) {
        return nullptr;
    }

    // Get mangled name
    std::string mangledName = getMangledName(record, staticMember, ctx);

    // Get C++ type
    QualType cppType = staticMember->getType();

    // TODO: Translate C++ type to C type
    // For now, use the same type (works for primitive types)
    QualType cType = cppType;

    // Get C translation unit from builder
    auto& cContext = ctx.getCContext();
    auto* cTU = cContext.getTranslationUnitDecl();

    // Create C VarDecl with extern storage class
    // Note: We create this in the C translation unit context
    VarDecl* cDecl = VarDecl::Create(
        cContext,                               // ASTContext
        cTU,                                    // DeclContext (translation unit)
        SourceLocation(),                       // Begin location
        SourceLocation(),                       // Location
        &cContext.Idents.get(mangledName),     // Identifier
        cType,                                  // Type
        nullptr,                                // TypeSourceInfo
        SC_Extern                               // Storage class: extern
    );

    // Preserve const qualifier if present
    // (already preserved in cType, but make explicit)

    return cDecl;
}

// ============================================================================
// Definition Generation (for implementation)
// ============================================================================

VarDecl* StaticMemberTranslator::generateStaticDefinition(
    VarDecl* staticMember,
    HandlerContext& ctx
) {
    if (!staticMember) {
        return nullptr;
    }

    // Get the owning class
    auto* record = dyn_cast<CXXRecordDecl>(staticMember->getDeclContext());
    if (!record) {
        return nullptr;
    }

    // Get mangled name (same as declaration)
    std::string mangledName = getMangledName(record, staticMember, ctx);

    // Get C++ type
    QualType cppType = staticMember->getType();

    // TODO: Translate C++ type to C type
    // For now, use the same type (works for primitive types)
    QualType cType = cppType;

    // Get initializer expression (if any)
    Expr* initializer = staticMember->getInit();

    // TODO: Translate initializer expression from C++ to C
    // For now, use the same expression
    Expr* cInitializer = initializer;

    // Get C translation unit from builder
    auto& cContext = ctx.getCContext();
    auto* cTU = cContext.getTranslationUnitDecl();

    // Create C VarDecl with SC_None (global scope, not extern)
    VarDecl* cDecl = VarDecl::Create(
        cContext,                               // ASTContext
        cTU,                                    // DeclContext (translation unit)
        SourceLocation(),                       // Begin location
        SourceLocation(),                       // Location
        &cContext.Idents.get(mangledName),     // Identifier
        cType,                                  // Type
        nullptr,                                // TypeSourceInfo
        SC_None                                 // Storage class: none (global)
    );

    // Set initializer if present
    if (cInitializer) {
        cDecl->setInit(cInitializer);
    }

    return cDecl;
}

// ============================================================================
// Definition Detection
// ============================================================================

bool StaticMemberTranslator::isStaticMemberDefinition(const VarDecl* varDecl) {
    if (!varDecl) {
        return false;
    }

    // Must be a static data member
    if (!varDecl->isStaticDataMember()) {
        return false;
    }

    // Must be at file scope (not a local variable)
    if (!varDecl->isFileVarDecl()) {
        return false;
    }

    // Must be a definition (has initializer or is the canonical definition)
    if (!varDecl->isThisDeclarationADefinition()) {
        return false;
    }

    return true;
}

CXXRecordDecl* StaticMemberTranslator::getOwningClass(const VarDecl* definition) {
    if (!definition) {
        return nullptr;
    }

    // The DeclContext should be the owning class
    auto* declContext = definition->getDeclContext();
    if (auto* record = dyn_cast<CXXRecordDecl>(declContext)) {
        // Cast away const - this is safe because we're just navigating the AST
        return const_cast<CXXRecordDecl*>(record);
    }

    return nullptr;
}

// ============================================================================
// Private Helpers
// ============================================================================

std::string StaticMemberTranslator::getMangledName(
    CXXRecordDecl* record,
    VarDecl* member,
    HandlerContext& ctx
) {
    // Use NameMangler to generate consistent mangled names
    NameMangler mangler(ctx.getCppContext());
    return mangler.mangleStaticMember(record, member);
}

} // namespace cpptoc
