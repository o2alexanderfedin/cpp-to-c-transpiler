/**
 * @file RecordHandler.cpp
 * @brief Implementation of RecordHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle struct/class translation.
 * Translates C++ structs and classes to C structs with field translation.
 * Handles nested structs with name mangling (Outer_Inner pattern).
 */

#include "dispatch/RecordHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "CNodeBuilder.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void RecordHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &RecordHandler::canHandle,
        &RecordHandler::handleRecord
    );
}

bool RecordHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Accept both plain struct (Record) and class (CXXRecord)
    // Use exact type checking (getKind) to match only these types
    return D->getKind() == clang::Decl::Record ||
           D->getKind() == clang::Decl::CXXRecord;
}

void RecordHandler::handleRecord(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert((D->getKind() == clang::Decl::Record || D->getKind() == clang::Decl::CXXRecord)
           && "Must be RecordDecl or CXXRecordDecl");

    const auto* cppRecord = llvm::cast<clang::RecordDecl>(D);

    // Check if already translated (avoid duplicates)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    if (declMapper.hasCreated(cppRecord)) {
        llvm::outs() << "[RecordHandler] Already translated struct/class: "
                     << cppRecord->getNameAsString() << " (skipping)\n";
        return;
    }

    // Extract struct/class properties
    std::string name = cppRecord->getNameAsString();

    // Check if this is a nested struct and compute mangled name
    std::string mangledName = name;

    // Check for namespace parent (apply namespace prefix)
    if (const auto* nsDecl = llvm::dyn_cast<clang::NamespaceDecl>(cppRecord->getDeclContext())) {
        std::string nsPrefix = cpptoc::NamespaceHandler::getNamespacePath(nsDecl);
        if (!nsPrefix.empty()) {
            mangledName = nsPrefix + "__" + name;
            llvm::outs() << "[RecordHandler] Applied namespace prefix: "
                         << name << " → " << mangledName << "\n";
        }
    }
    // Check for nested struct parent (apply struct name prefix)
    else if (const auto* parentDC = llvm::dyn_cast<clang::RecordDecl>(cppRecord->getDeclContext())) {
        std::string parentName = parentDC->getNameAsString();
        // Skip if parent has the same name (self-reference / Clang artifact)
        if (parentName != name) {
            mangledName = getMangledName(parentName, name);
            llvm::outs() << "[RecordHandler] Detected nested struct: "
                         << parentName << "::" << name << " → " << mangledName << "\n";
        }
    }

    // Handle forward declaration first (before checking polymorphism)
    // isPolymorphic() requires a complete definition
    if (!cppRecord->isCompleteDefinition()) {
        llvm::outs() << "[RecordHandler] Creating forward declaration for: " << mangledName << "\n";

        clang::CNodeBuilder builder(cASTContext);
        clang::RecordDecl* cForwardDecl = builder.forwardStructDecl(mangledName);

        // Store mapping
        declMapper.setCreated(cppRecord, cForwardDecl);

        // Get target path and register location
        std::string targetPath = disp.getTargetPath(cppASTContext, D);
        cpptoc::PathMapper& pathMapper = disp.getPathMapper();
        pathMapper.setNodeLocation(cForwardDecl, targetPath);

        llvm::outs() << "[RecordHandler] Created forward declaration: " << mangledName << "\n";
        return;
    }

    // Skip polymorphic classes (vtables not supported yet)
    // IMPORTANT: Check this AFTER forward declaration check
    // isPolymorphic() requires a complete definition
    if (const auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord)) {
        if (cxxRecord->isPolymorphic()) {
            llvm::errs() << "[RecordHandler] Warning: Skipping polymorphic class (vtables not supported): "
                         << name << "\n";
            return;
        }
    }

    // Create identifier for struct name (use mangled name for nested structs)
    clang::IdentifierInfo& II = cASTContext.Idents.get(mangledName);

    // Create C struct (normalize class → struct)
    // Always use Struct tag (C has no classes)
    clang::RecordDecl* cRecord = clang::RecordDecl::Create(
        cASTContext,
#if LLVM_VERSION_MAJOR >= 16
        clang::TagTypeKind::Struct,
#else
        clang::TTK_Struct,
#endif
        cASTContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II
    );

    assert(cRecord && "Failed to create C RecordDecl");

    // Store mapping EARLY (before translating children to handle recursive references)
    declMapper.setCreated(cppRecord, cRecord);

    // Start definition
    cRecord->startDefinition();

    // Translate nested structs FIRST (before fields, so they're available for field types)
    translateNestedStructs(cppRecord, disp, cppASTContext, cASTContext, name);

    // Translate fields
    std::vector<clang::FieldDecl*> cFields = translateFields(cppRecord, cRecord, disp, cppASTContext, cASTContext);

    // Add fields to struct
    for (auto* cField : cFields) {
        cField->setDeclContext(cRecord);
        cRecord->addDecl(cField);
    }

    // Complete definition
    cRecord->completeDefinition();

    // Get target path for this C++ source file
    std::string targetPath = disp.getTargetPath(cppASTContext, D);

    // Get or create C TranslationUnit for this target file
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTU && "Failed to get/create C TranslationUnit");

    // Add C struct to C TranslationUnit
    cRecord->setDeclContext(cTU);
    cTU->addDecl(cRecord);

    // Register node location in PathMapper for tracking
    pathMapper.setNodeLocation(cRecord, targetPath);

    // Debug output for verification
    llvm::outs() << "[RecordHandler] Translated struct/class: " << name
                 << (name != mangledName ? " → " + mangledName : "")
                 << " (" << cFields.size() << " fields) → " << targetPath << "\n";
}

std::vector<clang::FieldDecl*> RecordHandler::translateFields(
    const clang::RecordDecl* cppRecord,
    clang::RecordDecl* cRecord,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::FieldDecl*> cFields;

    // Iterate through all fields
    for (const auto* cppField : cppRecord->fields()) {
        // Extract field properties
        std::string fieldName = cppField->getNameAsString();
        clang::QualType cppFieldType = cppField->getType();

        // Dispatch field type to TypeHandler
        const clang::Type* cppFieldTypePtr = cppFieldType.getTypePtr();
        bool typeHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppFieldTypePtr));

        // Retrieve translated type from TypeMapper
        cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();
        clang::QualType cFieldType = typeMapper.getCreated(cppFieldTypePtr);

        // If TypeHandler didn't handle this type (pass-through), use original type
        if (cFieldType.isNull()) {
            cFieldType = cppFieldType;
            llvm::outs() << "[RecordHandler] TypeHandler pass-through for field type: "
                         << cppFieldType.getAsString() << "\n";
        }

        // Create identifier for field name
        clang::IdentifierInfo& fieldII = cASTContext.Idents.get(fieldName);

        // Create C FieldDecl
        clang::FieldDecl* cField = clang::FieldDecl::Create(
            cASTContext,
            cRecord,  // Parent record
            clang::SourceLocation(),
            clang::SourceLocation(),
            &fieldII,
            cFieldType,
            cASTContext.getTrivialTypeSourceInfo(cFieldType),
            nullptr,  // No bit width
            false,    // Not mutable
            clang::ICIS_NoInit
        );

        assert(cField && "Failed to create C FieldDecl");

        cFields.push_back(cField);

        llvm::outs() << "[RecordHandler] Translated field: " << fieldName
                     << " (" << cppFieldType.getAsString() << " → "
                     << cFieldType.getAsString() << ")\n";
    }

    return cFields;
}

void RecordHandler::translateNestedStructs(
    const clang::RecordDecl* cppRecord,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const std::string& outerName
) {
    // Find nested RecordDecls
    for (const auto* D : cppRecord->decls()) {
        if (const auto* nestedRecord = llvm::dyn_cast<clang::RecordDecl>(D)) {
            // Skip self-reference (struct detecting itself as nested)
            // Use canonical declarations for comparison (handles definition vs declaration)
            if (nestedRecord->getCanonicalDecl() == cppRecord->getCanonicalDecl()) {
                continue;
            }

            std::string innerName = nestedRecord->getNameAsString();

            // Skip anonymous structs (need special handling - future phase)
            if (innerName.empty()) {
                llvm::outs() << "[RecordHandler] Warning: Skipping anonymous nested struct\n";
                continue;
            }

            llvm::outs() << "[RecordHandler] Translating nested struct: "
                         << outerName << "::" << innerName << "\n";

            // Dispatch nested struct to RecordHandler (recursive)
            // RecordHandler will handle the name mangling
            bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::RecordDecl*>(nestedRecord));

            if (!handled) {
                llvm::errs() << "[RecordHandler] Warning: Failed to translate nested struct: "
                             << innerName << "\n";
            }
        }
    }
}

std::string RecordHandler::getMangledName(const std::string& outerName, const std::string& innerName) {
    return outerName + "__" + innerName;
}

} // namespace cpptoc
