/**
 * @file StaticDataMemberHandler.cpp
 * @brief Implementation of StaticDataMemberHandler (Phase 49)
 *
 * Translates C++ static data members to C global variables with mangled names.
 */

#include "dispatch/StaticDataMemberHandler.h"
#include "NameMangler.h"
#include "mapping/DeclMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/PathMapper.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

using namespace clang;

namespace cpptoc {

// ============================================================================
// Registration
// ============================================================================

void StaticDataMemberHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &StaticDataMemberHandler::canHandle,
        &StaticDataMemberHandler::handleStaticDataMember
    );
}

// ============================================================================
// Predicate
// ============================================================================

bool StaticDataMemberHandler::canHandle(const Decl* D) {
    assert(D && "Declaration must not be null");

    // Must be a VarDecl
    if (D->getKind() != Decl::Var) {
        return false;
    }

    const auto* varDecl = llvm::cast<VarDecl>(D);

    // Must be a static data member (class variable, not instance field)
    if (!varDecl->isStaticDataMember()) {
        return false;
    }

    return true;
}

// ============================================================================
// Visitor
// ============================================================================

void StaticDataMemberHandler::handleStaticDataMember(
    const CppToCVisitorDispatcher& disp,
    const ASTContext& cppASTContext,
    ASTContext& cASTContext,
    const Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == Decl::Var && "Must be VarDecl");

    const auto* cppStaticMember = llvm::cast<VarDecl>(D);

    // Verify it's a static data member
    if (!cppStaticMember->isStaticDataMember()) {
        llvm::errs() << "[StaticDataMemberHandler] Not a static data member - should be filtered by canHandle\n";
        return;
    }

    // Check if already translated (avoid duplicates)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    if (declMapper.hasCreated(cppStaticMember)) {
        return;  // Already translated
    }

    // Get the owning class
    auto* record = llvm::dyn_cast<CXXRecordDecl>(cppStaticMember->getDeclContext());
    if (!record) {
        llvm::errs() << "[StaticDataMemberHandler] Static member has no owning class\n";
        return;
    }

    // Get mangled name using NameMangler
    std::string mangledName = cpptoc::mangle_static_member(cppStaticMember);

    // Get C++ type
    QualType cppType = cppStaticMember->getType();

    // TODO: Translate C++ type to C type via TypeHandler dispatch
    // For now, use the same type (works for primitive types)
    QualType cType = cppType;

    // Determine storage class based on whether this is a declaration or definition
    // - In-class declaration: SC_Extern (extern int ClassName__member;)
    // - Out-of-class definition: SC_None (int ClassName__member = 0;)
    StorageClass storageClass = SC_Extern;

    // Check if this is a definition (has initializer or is marked as definition)
    bool isDefinition = cppStaticMember->isThisDeclarationADefinition();
    if (isDefinition) {
        storageClass = SC_None;  // Global scope, not extern
    }

    // Get target path and C TranslationUnit
    std::string targetPath = disp.getCurrentTargetPath();  // Use current path set by TranslationUnitHandler
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);

    // Create C VarDecl
    VarDecl* cStaticMember = VarDecl::Create(
        cASTContext,                               // ASTContext
        cTU,                                       // DeclContext (translation unit)
        SourceLocation(),                          // Begin location
        SourceLocation(),                          // Location
        &cASTContext.Idents.get(mangledName),     // Identifier (mangled name)
        cType,                                     // Type
        nullptr,                                   // TypeSourceInfo
        storageClass                               // SC_Extern or SC_None
    );

    assert(cStaticMember && "Failed to create C VarDecl for static data member");

    // Handle initializer - check for it regardless of isDefinition
    // For const static members with in-class initializers like:
    //   static const int MAX_SIZE = 1024;
    // The isThisDeclarationADefinition() returns false, but getInit() returns the initializer
    const Expr* cppInitializer = cppStaticMember->getInit();
    if (cppInitializer) {
        // Dispatch the initializer expression to translate it to C
        cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

        // Dispatch the C++ initializer expression
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<Expr*>(cppInitializer));

        if (handled && exprMapper.hasCreated(cppInitializer)) {
            // Get the translated C initializer
            Expr* cInitializer = exprMapper.getCreated(cppInitializer);
            cStaticMember->setInit(cInitializer);

            llvm::outs() << "[StaticDataMemberHandler] Initializer translated successfully\n";
        } else {
            llvm::errs() << "[StaticDataMemberHandler] WARNING: Failed to translate initializer expression\n";
            llvm::errs() << "  This may indicate that the necessary expression handlers are not registered.\n";
            llvm::errs() << "  For literal initializers, ensure LiteralHandler is registered.\n";
        }

        // If we have an initializer, this should be treated as a definition (SC_None)
        if (!isDefinition) {
            cStaticMember->setStorageClass(SC_None);
        }
    }

    // Store mapping in DeclMapper
    declMapper.setCreated(cppStaticMember, cStaticMember);

    // Add to C TranslationUnit
    cStaticMember->setDeclContext(cTU);
    cTU->addDecl(cStaticMember);

    // Register location in PathMapper
    pathMapper.setNodeLocation(cStaticMember, targetPath);

    // Debug output
    const char* declType = isDefinition ? "definition" : "declaration";
    llvm::outs() << "[StaticDataMemberHandler] Translated " << declType << ": "
                 << record->getNameAsString() << "::" << cppStaticMember->getNameAsString()
                 << " → " << mangledName << " (" << targetPath << ")\n";
}

// ============================================================================
// Utility Methods (No Dispatcher Dependencies)
// ============================================================================

std::vector<VarDecl*> StaticDataMemberHandler::detectStaticMembers(
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
        if (auto* varDecl = llvm::dyn_cast<VarDecl>(decl)) {
            // Check if it's a static data member
            if (varDecl->isStaticDataMember()) {
                staticMembers.push_back(varDecl);
            }
        }
    }

    return staticMembers;
}

bool StaticDataMemberHandler::isStaticMemberDefinition(const VarDecl* varDecl) {
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

CXXRecordDecl* StaticDataMemberHandler::getOwningClass(const VarDecl* definition) {
    if (!definition) {
        return nullptr;
    }

    // The DeclContext should be the owning class
    auto* declContext = definition->getDeclContext();
    if (auto* record = llvm::dyn_cast<CXXRecordDecl>(declContext)) {
        // Cast away const - this is safe because we're just navigating the AST
        return const_cast<CXXRecordDecl*>(record);
    }

    return nullptr;
}

} // namespace cpptoc
