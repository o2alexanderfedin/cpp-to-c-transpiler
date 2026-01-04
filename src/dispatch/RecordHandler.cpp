/**
 * @file RecordHandler.cpp
 * @brief Implementation of RecordHandler dispatcher pattern
 *
 * Phase 4: NameMangler Free Function API
 * - Uses cpptoc::mangle_class() free function for all class/struct name mangling
 * - Eliminated NameMangler instantiation and const_cast calls
 * - Simplified API: pass const pointers directly to free functions
 * - Consistent with InstanceMethodHandler and StaticMethodHandler
 *
 * Integrates with CppToCVisitorDispatcher to handle struct/class translation.
 * Translates C++ structs and classes to C structs with field translation.
 * Handles nested structs with name mangling (Outer__Inner pattern via NameMangler).
 */

#include "dispatch/RecordHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "CNodeBuilder.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "NameMangler.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Index/USRGeneration.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <set>

namespace cpptoc {

// Global set to track which structs/classes have been translated using USR
// USR (Unified Symbol Resolution) is unique across translation units
static std::set<std::string> translatedRecordUSRs;

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

    // Check if this struct logically belongs to the current file being processed
    // MUST CHECK THIS FIRST before marking as translated!
    // Compare base filenames (without extension) to handle src/*.cpp vs include/*.h split
    std::string currentTargetPath = disp.getCurrentTargetPath();
    std::string structTargetPath = disp.getTargetPath(cppASTContext, cppRecord);

    // Extract base filenames (e.g., "Vector3D" from "transpiled/src/Vector3D.c")
    auto getBaseName = [](const std::string& path) -> std::string {
        size_t lastSlash = path.find_last_of("/\\");
        std::string filename = (lastSlash == std::string::npos) ? path : path.substr(lastSlash + 1);
        size_t lastDot = filename.find_last_of('.');
        return (lastDot == std::string::npos) ? filename : filename.substr(0, lastDot);
    };

    std::string currentBase = getBaseName(currentTargetPath);
    std::string structBase = getBaseName(structTargetPath);

    if (currentBase != structBase) {
        llvm::outs() << "[RecordHandler] Struct/class " << cppRecord->getNameAsString()
                     << " belongs to different file (" << structBase << " vs " << currentBase
                     << "), skipping (will be translated in its own file)\n";
        return;
    }

    // Generate USR (Unified Symbol Resolution) to identify this struct/class uniquely across TUs
    llvm::SmallString<128> USR;
    if (clang::index::generateUSRForDecl(cppRecord, USR)) {
        // Failed to generate USR - fall back to name-based check (may have duplicates)
        llvm::outs() << "[RecordHandler] WARNING: Failed to generate USR for "
                     << cppRecord->getNameAsString() << "\n";
    } else {
        std::string usrStr = USR.str().str();

        // Check if already translated using USR (works across different translation units)
        if (translatedRecordUSRs.find(usrStr) != translatedRecordUSRs.end()) {
            llvm::outs() << "[RecordHandler] Already translated struct/class: "
                         << cppRecord->getNameAsString() << " (USR: " << usrStr << ") (skipping)\n";
            return;
        }

        // Mark as translated (ONLY after file origin check passed!)
        translatedRecordUSRs.insert(usrStr);
    }

    // Use canonical declaration for DeclMapper (still needed for within-TU lookups)
    const auto* canonicalRecord = cppRecord->getCanonicalDecl();

    // Also store in DeclMapper for within-TU lookups
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    if (declMapper.hasCreated(canonicalRecord)) {
        llvm::outs() << "[RecordHandler] Already translated struct/class (DeclMapper): "
                     << cppRecord->getNameAsString() << " (skipping)\n";
        return;
    }

    // Extract struct/class properties
    std::string name = cppRecord->getNameAsString();

    // Phase 4: Use NameMangler free function API (mangle_class)
    // mangle_class handles both namespace prefixes and nested struct mangling
    std::string mangledName;
    if (const auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord)) {
        // Use new free function API - no instantiation, no const_cast needed
        mangledName = cpptoc::mangle_class(cxxRecord);
    } else {
        // Plain C struct (RecordDecl) - use simple name
        // TODO: May need to enhance NameMangler to handle RecordDecl too
        mangledName = name;
    }

    if (name != mangledName) {
        llvm::outs() << "[RecordHandler] Mangled struct/class name: "
                     << name << " → " << mangledName << "\n";
    }

    // Handle forward declaration first (before checking polymorphism)
    // isPolymorphic() requires a complete definition
    if (!cppRecord->isCompleteDefinition()) {
        llvm::outs() << "[RecordHandler] Creating forward declaration for: " << mangledName << "\n";

        clang::CNodeBuilder builder(cASTContext);
        clang::RecordDecl* cForwardDecl = builder.forwardStructDecl(mangledName);

        // Store mapping using canonical declaration
        declMapper.setCreated(canonicalRecord, cForwardDecl);

        // Get current target path and register location
        std::string targetPath = disp.getCurrentTargetPath();
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
        clang::TTK_Struct,
#else
        clang::TTK_Struct,
#endif
        cASTContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II
    );

    assert(cRecord && "Failed to create C RecordDecl");

    // Store mapping EARLY using canonical declaration (before translating children to handle recursive references)
    declMapper.setCreated(canonicalRecord, cRecord);

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

    // Get current target path (where current source file is being transpiled)
    // This ensures structs from headers are emitted to the source file's C_TU
    std::string targetPath = disp.getCurrentTargetPath();

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

// Phase 4: Migrated to NameMangler free function API (mangle_class)
// Free functions provide unified name mangling for all declarations (classes, methods, functions)
// and handle both namespaces (single _) and nested structs (double __) correctly
// Benefits: no instantiation overhead, no const_cast needed, cleaner code

} // namespace cpptoc
