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
#include "SourceLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "llvm/Config/llvm-config.h" // For LLVM_VERSION_MAJOR
#include "NameMangler.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Index/USRGeneration.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include "VirtualInheritanceAnalyzer.h"
#include "MultipleInheritanceAnalyzer.h"
#include "VTTGenerator.h"
#include "VtableGenerator.h"
#include "VirtualMethodAnalyzer.h"
#include "OverrideResolver.h"
#include <cassert>
#include <functional>
#include <set>
#include <string>

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

    // Special case: In test scenarios with in-memory sources (buildASTFromCode),
    // Clang may assign different source locations to TU vs declarations
    // (e.g., TU gets "<stdin>", struct gets "input.cc")
    // Treat these as matching by checking if either path contains <stdin>
    bool isTestScenario = (currentTargetPath.find("<stdin>") != std::string::npos ||
                           structTargetPath.find("<stdin>") != std::string::npos ||
                           currentTargetPath.find("/input.c") != std::string::npos ||
                           structTargetPath.find("/input.c") != std::string::npos);

    if (!isTestScenario && currentBase != structBase) {
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

    // Get target path early for both forward declarations and complete definitions
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, cppRecord);
    }
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();

    // Handle forward declaration first (before checking polymorphism)
    // isPolymorphic() requires a complete definition
    if (!cppRecord->isCompleteDefinition()) {
        llvm::outs() << "[RecordHandler] Creating forward declaration for: " << mangledName << "\n";

        clang::CNodeBuilder builder(cASTContext);
        clang::RecordDecl* cForwardDecl = builder.forwardStructDecl(mangledName);

        // Store mapping using canonical declaration
        declMapper.setCreated(canonicalRecord, cForwardDecl);

        // Register location with target path
        pathMapper.setNodeLocation(cForwardDecl, targetPath);

        llvm::outs() << "[RecordHandler] Created forward declaration: " << mangledName << "\n";
        return;
    }

    // Phase 2: Check if dual layout generation is needed
    const clang::CXXRecordDecl* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord);
    if (cxxRecord && needsDualLayout(cxxRecord)) {
        llvm::outs() << "[RecordHandler] Generating dual layout for " << name << " (virtual inheritance detected)\n";

        // Generate BOTH layouts per Itanium C++ ABI:
        // 1. Base-subobject layout (ClassName__base) - for use as base class
        clang::RecordDecl* baseLayout = generateBaseSubobjectLayout(cxxRecord, cppASTContext, cASTContext, disp);

        // 2. Complete-object layout (ClassName) - for most-derived objects
        clang::RecordDecl* completeLayout = generateCompleteObjectLayout(cxxRecord, cppASTContext, cASTContext, disp);

        if (!baseLayout || !completeLayout) {
            llvm::errs() << "[RecordHandler] ERROR: Failed to generate dual layout for " << name << "\n";
            return;
        }

        // Store both layouts in DeclMapper
        // The complete-object layout is the "primary" mapping for most contexts
        declMapper.setCreated(canonicalRecord, completeLayout);
        if (cppRecord != canonicalRecord) {
            declMapper.setCreated(cppRecord, completeLayout);
        }

        // Get target path and TU
        clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
        assert(cTU && "Failed to get/create C TranslationUnit");

        // Add BOTH structs to C TranslationUnit
        baseLayout->setDeclContext(cTU);
        cTU->addDecl(baseLayout);
        pathMapper.setNodeLocation(baseLayout, targetPath);

        completeLayout->setDeclContext(cTU);
        cTU->addDecl(completeLayout);
        pathMapper.setNodeLocation(completeLayout, targetPath);

        // Dispatch member declarations (constructors, methods, destructors)
        for (auto* memberDecl : cxxRecord->decls()) {
            disp.dispatch(cppASTContext, cASTContext, memberDecl);
        }

        // Check if class has any explicit constructors
        bool hasExplicitConstructor = false;
        for (auto* ctor : cxxRecord->ctors()) {
            if (!ctor->isImplicit()) {
                hasExplicitConstructor = true;
                break;
            }
        }

        // If no explicit constructors, generate implicit default C1/C2 constructors
        if (!hasExplicitConstructor) {
            llvm::outs() << "[RecordHandler] Class " << name
                         << " has virtual inheritance but no explicit constructors - generating implicit C1/C2\n";
            generateImplicitC1Constructor(cxxRecord, cppASTContext, cASTContext, disp);
            generateImplicitC2Constructor(cxxRecord, cppASTContext, cASTContext, disp);
        }

        llvm::outs() << "[RecordHandler] Successfully generated dual layout for " << name << ":\n";
        llvm::outs() << "  - Base-subobject: " << mangledName << "__base\n";
        llvm::outs() << "  - Complete-object: " << mangledName << "\n";

        return;  // Early return - dual layout path complete
    }

    // SINGLE LAYOUT PATH (existing code continues below)
    // For classes without virtual inheritance, generate single layout

    // Create identifier for struct name (use mangled name for nested structs)
    clang::IdentifierInfo& II = cASTContext.Idents.get(mangledName);

    // Get source location from SourceLocationMapper
    clang::SourceLocation targetLoc = disp.getTargetSourceLocation(cppASTContext, cppRecord);

    // Create C struct (normalize class → struct)
    // Always use Struct tag (C has no classes)
    // API change: LLVM 15 uses TTK_Struct, LLVM 16+ uses Struct (enum class)
    clang::RecordDecl* cRecord = clang::RecordDecl::Create(
        cASTContext,
        #if LLVM_VERSION_MAJOR >= 16
        clang::TagTypeKind::Struct,
        #else
        clang::TTK_Struct,
        #endif
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &II
    );

    assert(cRecord && "Failed to create C RecordDecl");

    // Store mapping EARLY using canonical declaration (before translating children to handle recursive references)
    declMapper.setCreated(canonicalRecord, cRecord);

    // ALSO store using the original cppRecord pointer (in case caller uses non-canonical decl)
    // This handles cases where code looks up using the complete definition instead of canonical
    if (cppRecord != canonicalRecord) {
        declMapper.setCreated(cppRecord, cRecord);
    }

    // Start definition
    cRecord->startDefinition();

    // Analyze virtual inheritance (if applicable) - reuse cxxRecord from dual layout check above
    bool hasVirtualBases = false;
    std::vector<const clang::CXXRecordDecl*> virtualBases;
    VirtualInheritanceAnalyzer viAnalyzer;

    if (cxxRecord) {
        viAnalyzer.analyzeClass(cxxRecord);

        hasVirtualBases = viAnalyzer.hasVirtualBases(cxxRecord);

        if (hasVirtualBases) {
            virtualBases = viAnalyzer.getVirtualBases(cxxRecord);
            llvm::outs() << "[RecordHandler] Class " << name
                         << " has " << virtualBases.size()
                         << " virtual base(s)\n";
        }
    }

    // Translate nested structs FIRST (before fields, so they're available for field types)
    translateNestedStructs(cppRecord, disp, cppASTContext, cASTContext, name);

    // Inject vbptr field for classes with virtual bases
    std::vector<clang::FieldDecl*> injectedFields;
    if (hasVirtualBases) {
        // Create vbptr field: const void** vbptr;
        clang::QualType vbptrType = cASTContext.getPointerType(
            cASTContext.getPointerType(cASTContext.VoidTy.withConst())
        );

        clang::IdentifierInfo& vbptrII = cASTContext.Idents.get("vbptr");

        clang::FieldDecl* vbptrField = clang::FieldDecl::Create(
            cASTContext,
            cRecord,
            targetLoc,
            targetLoc,
            &vbptrII,
            vbptrType,
            cASTContext.getTrivialTypeSourceInfo(vbptrType),
            nullptr,  // No bit width
            false,    // Not mutable
            clang::ICIS_NoInit
        );

        vbptrField->setAccess(clang::AS_public);
        vbptrField->setDeclContext(cRecord);
        injectedFields.push_back(vbptrField);

        llvm::outs() << "[RecordHandler] Injected vbptr field for virtual inheritance\n";
    }

    // Translate fields
    std::vector<clang::FieldDecl*> cFields = translateFields(cppRecord, cRecord, disp, cppASTContext, cASTContext);

    // Combine injected fields and regular fields
    std::vector<clang::FieldDecl*> allFields;
    allFields.insert(allFields.end(), injectedFields.begin(), injectedFields.end());
    allFields.insert(allFields.end(), cFields.begin(), cFields.end());

    // Add base class fields (both virtual and non-virtual)
    // In C, we need to flatten the inheritance hierarchy by copying base class fields
    //
    // CRITICAL VIRTUAL INHERITANCE RULE (Itanium C++ ABI):
    // - Virtual base fields should ONLY be in MOST-DERIVED classes
    // - Intermediate classes with virtual bases should NOT inline those virtual base fields
    // - Only non-virtual base fields should be inlined in intermediate classes
    //
    // Example (Diamond Inheritance):
    //   struct A { int a; };
    //   struct B : virtual A { int b; };  // B should NOT have 'a' field
    //   struct C : virtual A { int c; };  // C should NOT have 'a' field
    //   struct D : B, C { int d; };       // D SHOULD have 'a' field (most-derived)
    if (cxxRecord && cxxRecord->getNumBases() > 0) {
        // Track field names already added to avoid duplicates (for virtual bases)
        std::set<std::string> addedFieldNames;
        for (const auto& existingField : allFields) {
            addedFieldNames.insert(existingField->getNameAsString());
        }

        // Collect all virtual bases in the hierarchy (direct + indirect)
        std::set<const clang::CXXRecordDecl*> allVirtualBases;

        // Helper: recursively collect virtual bases
        std::function<void(const clang::CXXRecordDecl*)> collectVirtualBases;
        collectVirtualBases = [&](const clang::CXXRecordDecl* record) {
            for (const auto& base : record->bases()) {
                if (const clang::CXXRecordDecl* baseRecord = base.getType()->getAsCXXRecordDecl()) {
                    if (base.isVirtual()) {
                        allVirtualBases.insert(baseRecord->getCanonicalDecl());
                    }
                    // Recurse to collect indirect virtual bases
                    collectVirtualBases(baseRecord);
                }
            }
        };
        collectVirtualBases(cxxRecord);

        // Determine if this class should inline virtual base fields
        //
        // Itanium C++ ABI Rule:
        // - Virtual base fields should ONLY be in the MOST-DERIVED class
        // - Intermediate classes (used as bases of other classes) should NOT have virtual base fields
        //
        // Analysis of inheritance patterns:
        // 1. SimpleVirtualBase (Derived : virtual Base):
        //    - Derived has DIRECT virtual base Base, no non-virtual bases
        //    - Derived is NOT polymorphic (no virtual methods)
        //    - Derived is likely a LEAF class → should inline Base fields
        //
        // 2. Diamond (D : B,C; B : virtual A; C : virtual A):
        //    - B has DIRECT virtual base A, no non-virtual bases, IS polymorphic → intermediate class
        //    - C has DIRECT virtual base A, no non-virtual bases, IS polymorphic → intermediate class
        //    - D has INDIRECT virtual bases (through B,C), has non-virtual bases with vbases → most-derived
        //
        // Heuristic:
        // - If class has non-virtual bases with virtual bases → inline INDIRECT virtual bases (diamond D case)
        // - If class has ONLY virtual bases AND is NOT polymorphic → inline them (leaf class)
        // - Otherwise → DON'T inline (intermediate class)

        bool hasNonVirtualBases = false;
        bool hasNonVirtualBasesWithVirtualBases = false;
        bool hasDirectVirtualBases = cxxRecord->getNumVBases() > 0;

        for (const auto& base : cxxRecord->bases()) {
            if (!base.isVirtual()) {
                hasNonVirtualBases = true;
                if (const clang::CXXRecordDecl* baseRecord = base.getType()->getAsCXXRecordDecl()) {
                    if (baseRecord->getNumVBases() > 0) {
                        hasNonVirtualBasesWithVirtualBases = true;
                        break;
                    }
                }
            }
        }

        // Should inline virtual base fields if:
        // 1. Has non-virtual bases with virtual bases (most-derived in diamond), OR
        // 2. Has ONLY direct virtual bases (no non-virtual bases) - assume leaf class
        //
        // Note: This is a heuristic. Ideally we'd generate both base-subobject and complete-object
        // layouts per Itanium C++ ABI, but that requires significant refactoring.
        bool isMostDerivedForVirtualInheritance =
            hasNonVirtualBasesWithVirtualBases ||
            (hasDirectVirtualBases && !hasNonVirtualBases);

        llvm::outs() << "[RecordHandler] Class " << cxxRecord->getNameAsString()
                     << (isMostDerivedForVirtualInheritance ? " IS most-derived" : " is NOT most-derived")
                     << " for virtual inheritance\n";

        // First, handle non-virtual bases (always copy their fields, but SKIP virtual base fields)
        for (const auto& base : cxxRecord->bases()) {
            if (base.isVirtual()) continue;  // Skip virtual bases for now

            const clang::CXXRecordDecl* baseRecord = base.getType()->getAsCXXRecordDecl();
            if (!baseRecord) continue;

            llvm::outs() << "[RecordHandler] Inlining fields from non-virtual base: "
                         << baseRecord->getNameAsString() << "\n";

            // Look up the C struct for this base
            cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
            if (declMapper.hasCreated(baseRecord)) {
                clang::RecordDecl* cBaseRecord = llvm::cast<clang::RecordDecl>(declMapper.getCreated(baseRecord));

                // Copy fields from non-virtual base, but SKIP fields that came from virtual bases
                // (those will be inlined separately if this is the most-derived class)
                for (auto* baseField : cBaseRecord->fields()) {
                    std::string fieldName = baseField->getNameAsString();

                    // Skip vbptr (will be inherited implicitly)
                    if (fieldName == "vbptr") {
                        llvm::outs() << "[RecordHandler] Skipping vbptr field from base\n";
                        continue;
                    }

                    // Check for duplicates
                    if (addedFieldNames.count(fieldName) > 0) {
                        llvm::outs() << "[RecordHandler] Skipping duplicate field from non-virtual base: " << fieldName << "\n";
                        continue;
                    }

                    clang::FieldDecl* copiedField = clang::FieldDecl::Create(
                        cASTContext,
                        cRecord,
                        targetLoc,
                        targetLoc,
                        baseField->getIdentifier(),
                        baseField->getType(),
                        baseField->getTypeSourceInfo(),
                        nullptr,  // No bit width
                        false,    // Not mutable
                        clang::ICIS_NoInit
                    );

                    copiedField->setAccess(clang::AS_public);
                    copiedField->setDeclContext(cRecord);
                    allFields.push_back(copiedField);
                    addedFieldNames.insert(fieldName);

                    llvm::outs() << "[RecordHandler] Inlined non-virtual base field: " << fieldName << "\n";
                }
            }
        }

        // Second, handle virtual bases (ONLY if this is the most-derived class)
        // Intermediate classes should NOT inline virtual base fields
        if (isMostDerivedForVirtualInheritance) {
            llvm::outs() << "[RecordHandler] Inlining virtual base fields (most-derived class)\n";

            for (const clang::CXXRecordDecl* vbaseRecord : allVirtualBases) {
                llvm::outs() << "[RecordHandler] Inlining fields from virtual base: "
                             << vbaseRecord->getNameAsString() << "\n";

                // Look up the C struct for this virtual base
                cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
                if (declMapper.hasCreated(vbaseRecord)) {
                    clang::RecordDecl* cVbaseRecord = llvm::cast<clang::RecordDecl>(declMapper.getCreated(vbaseRecord));

                    // Get the ORIGINAL C++ fields
                    if (vbaseRecord->getDefinition()) {
                        for (auto* originalField : vbaseRecord->fields()) {
                            std::string fieldName = originalField->getNameAsString();

                            // Skip if this field name was already added
                            if (addedFieldNames.count(fieldName) > 0) {
                                llvm::outs() << "[RecordHandler] Skipping duplicate virtual base field: " << fieldName << "\n";
                                continue;
                            }

                            // Find the corresponding C field in cVbaseRecord
                            clang::FieldDecl* cVbaseField = nullptr;
                            for (auto* field : cVbaseRecord->fields()) {
                                if (field->getNameAsString() == fieldName) {
                                    cVbaseField = field;
                                    break;
                                }
                            }

                            if (cVbaseField) {
                                // Create a new field with the same name and type
                                clang::FieldDecl* copiedField = clang::FieldDecl::Create(
                                    cASTContext,
                                    cRecord,
                                    targetLoc,
                                    targetLoc,
                                    cVbaseField->getIdentifier(),
                                    cVbaseField->getType(),
                                    cVbaseField->getTypeSourceInfo(),
                                    nullptr,  // No bit width
                                    false,    // Not mutable
                                    clang::ICIS_NoInit
                                );

                                copiedField->setAccess(clang::AS_public);
                                copiedField->setDeclContext(cRecord);
                                allFields.push_back(copiedField);
                                addedFieldNames.insert(fieldName);

                                llvm::outs() << "[RecordHandler] Inlined virtual base field: " << fieldName << "\n";
                            }
                        }
                    }
                } else {
                    llvm::outs() << "[RecordHandler] WARNING: Virtual base " << vbaseRecord->getNameAsString()
                                 << " not yet translated, cannot inline fields\n";
                }
            }
        } else {
            llvm::outs() << "[RecordHandler] Skipping virtual base field inlining (intermediate class)\n";
        }
    }

    // Add fields to struct
    for (auto* cField : allFields) {
        cField->setDeclContext(cRecord);
        cRecord->addDecl(cField);
    }

    // Complete definition
    cRecord->completeDefinition();

    // Generate VTT (Virtual Table Table) for classes with virtual bases
    if (hasVirtualBases && cxxRecord) {
        // Cast away const for ASTContext parameter (VTTGenerator requires non-const)
        VTTGenerator vttGen(const_cast<clang::ASTContext&>(cppASTContext), viAnalyzer);

        std::string vttCode = vttGen.generateVTT(cxxRecord);

        if (!vttCode.empty()) {
            // TODO: For now, log VTT generation. In future, emit to output file.
            llvm::outs() << "[RecordHandler] Generated VTT for " << name << ":\n"
                         << vttCode << "\n";

            // TODO: Create C AST nodes for VTT struct and instance
            // This requires extending CNodeBuilder with VTT generation methods
        }
    }

    // Task 5: Generate vtable with virtual base offsets for polymorphic classes with virtual bases
    if (cxxRecord && cxxRecord->isPolymorphic() && hasVirtualBases) {
        llvm::outs() << "[RecordHandler] Generating vtable with virtual base offsets for " << name << "\n";

        // Use VtableGenerator to generate vtable struct with virtual base offsets
        // Requires VirtualMethodAnalyzer and OverrideResolver
        VirtualMethodAnalyzer vmAnalyzer(const_cast<clang::ASTContext&>(cppASTContext));
        OverrideResolver overrideResolver(const_cast<clang::ASTContext&>(cppASTContext), vmAnalyzer);
        VtableGenerator vtableGen(const_cast<clang::ASTContext&>(cppASTContext), vmAnalyzer, &overrideResolver);

        std::string vtableCode = vtableGen.generateVtableWithVirtualBaseOffsets(cxxRecord, viAnalyzer);

        if (!vtableCode.empty()) {
            llvm::outs() << "[RecordHandler] Generated vtable with virtual base offsets for " << name << ":\n"
                         << vtableCode << "\n";

            // TODO: Create C AST nodes for vtable struct
            // TODO: Generate vtable instance initialization
            // For now, string-based code generation is acceptable (Phase 3 MVP)
        }
    }

    // Get or create C TranslationUnit for this target file
    // (targetPath already obtained above with SourceLocationMapper)
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTU && "Failed to get/create C TranslationUnit");

    // Add C struct to C TranslationUnit
    cRecord->setDeclContext(cTU);
    cTU->addDecl(cRecord);

    // Register node location in PathMapper for tracking
    pathMapper.setNodeLocation(cRecord, targetPath);

    // Dispatch member declarations (constructors, methods, destructors)
    // Only for C++ classes, not plain C structs
    if (cxxRecord) {
        for (auto* memberDecl : cxxRecord->decls()) {
            // Dispatch each member declaration to appropriate handler
            // ConstructorHandler, InstanceMethodHandler, VirtualMethodHandler, etc.
            disp.dispatch(cppASTContext, cASTContext, memberDecl);
        }
    }

    // Debug output for verification
    llvm::outs() << "[RecordHandler] Translated struct/class: " << name
                 << (name != mangledName ? " → " + mangledName : "")
                 << " (" << allFields.size() << " fields";
    if (hasVirtualBases) {
        llvm::outs() << ", including vbptr";
    }
    llvm::outs() << ") → " << targetPath << "\n";
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

        // Get source location from SourceLocationMapper
        clang::SourceLocation fieldTargetLoc = disp.getTargetSourceLocation(cppASTContext, cppRecord);

        // Create C FieldDecl
        clang::FieldDecl* cField = clang::FieldDecl::Create(
            cASTContext,
            cRecord,  // Parent record
            fieldTargetLoc,
            fieldTargetLoc,
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
    // Find truly nested RecordDecls (defined inside this struct, not forward decls)
    // cppRecord->decls() returns ALL declarations in this record, including:
    // 1. Truly nested structs (parent DeclContext is this record)
    // 2. Forward declarations of THIS struct (when forward decl precedes complete def)
    // We want only #1, so check:
    // - Is it a RecordDecl?
    // - Is its canonical decl DIFFERENT from outer's canonical (not self-reference)?
    // - Is its NAME different from outer's name (not forward decl of same struct)?
    for (const auto* D : cppRecord->decls()) {
        if (const auto* nestedRecord = llvm::dyn_cast<clang::RecordDecl>(D)) {
            // Skip self-reference: forward decl of same struct shares canonical with outer
            // Example: "struct Node; struct Node { ... };" - forward decl appears in complete def's decls()
            if (nestedRecord->getCanonicalDecl() == cppRecord->getCanonicalDecl()) {
                continue;
            }

            std::string innerName = nestedRecord->getNameAsString();

            // Also skip if names match (forward decl of same struct with different canonical)
            // This can happen when forward decl precedes complete def
            if (innerName == outerName) {
                continue;
            }

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

bool RecordHandler::needsDualLayout(const clang::CXXRecordDecl* cxxRecord) {
    if (!cxxRecord) return false;

    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(cxxRecord);

    // Needs dual layout if:
    // 1. Has virtual bases (direct or indirect), OR
    // 2. Is used as base in a virtual hierarchy (detected by VTT generation need)
    //
    // Per Itanium C++ ABI:
    // - Classes with virtual bases need both base-subobject and complete-object layouts
    // - Base-subobject layout (ClassName__base) excludes virtual base fields
    // - Complete-object layout (ClassName) includes virtual base fields
    return viAnalyzer.hasVirtualBases(cxxRecord) ||
           viAnalyzer.needsVTT(cxxRecord);
}

clang::RecordDecl* RecordHandler::generateBaseSubobjectLayout(
    const clang::CXXRecordDecl* cxxRecord,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const CppToCVisitorDispatcher& disp
) {
    if (!cxxRecord) return nullptr;

    // Get mangled name and add "__base" suffix
    std::string mangledName = cpptoc::mangle_class(cxxRecord) + "__base";

    // Get source location
    clang::SourceLocation targetLoc = disp.getTargetSourceLocation(cppASTContext, cxxRecord);

    // Create identifier
    clang::IdentifierInfo& II = cASTContext.Idents.get(mangledName);

    // Create C struct with "__base" suffix
    clang::RecordDecl* cRecord = clang::RecordDecl::Create(
        cASTContext,
        #if LLVM_VERSION_MAJOR >= 16
        clang::TagTypeKind::Struct,
        #else
        clang::TTK_Struct,
        #endif
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &II
    );

    if (!cRecord) return nullptr;

    // Start definition
    cRecord->startDefinition();

    // Analyze virtual inheritance
    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(cxxRecord);
    bool hasVirtualBases = viAnalyzer.hasVirtualBases(cxxRecord);

    std::vector<clang::FieldDecl*> allFields;

    // 1. Inject vbptr if needed (for classes with virtual bases)
    if (hasVirtualBases) {
        clang::QualType vbptrType = cASTContext.getPointerType(
            cASTContext.getPointerType(cASTContext.VoidTy.withConst())
        );

        clang::IdentifierInfo& vbptrII = cASTContext.Idents.get("vbptr");

        clang::FieldDecl* vbptrField = clang::FieldDecl::Create(
            cASTContext,
            cRecord,
            targetLoc,
            targetLoc,
            &vbptrII,
            vbptrType,
            cASTContext.getTrivialTypeSourceInfo(vbptrType),
            nullptr,  // No bit width
            false,    // Not mutable
            clang::ICIS_NoInit
        );

        vbptrField->setAccess(clang::AS_public);
        vbptrField->setDeclContext(cRecord);
        allFields.push_back(vbptrField);
    }

    // 2. Include non-virtual base fields (but NOT virtual base fields)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    std::set<std::string> addedFieldNames;

    for (const auto& base : cxxRecord->bases()) {
        if (base.isVirtual()) continue;  // Skip virtual bases

        const clang::CXXRecordDecl* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        // Look up the C struct for this base (might be __base or regular depending on its needs)
        if (declMapper.hasCreated(baseRecord)) {
            clang::RecordDecl* cBaseRecord = llvm::cast<clang::RecordDecl>(declMapper.getCreated(baseRecord));

            for (auto* baseField : cBaseRecord->fields()) {
                std::string fieldName = baseField->getNameAsString();

                // Skip vbptr and duplicates
                if (fieldName == "vbptr" || addedFieldNames.count(fieldName) > 0) {
                    continue;
                }

                clang::FieldDecl* copiedField = clang::FieldDecl::Create(
                    cASTContext,
                    cRecord,
                    targetLoc,
                    targetLoc,
                    baseField->getIdentifier(),
                    baseField->getType(),
                    baseField->getTypeSourceInfo(),
                    nullptr,  // No bit width
                    false,    // Not mutable
                    clang::ICIS_NoInit
                );

                copiedField->setAccess(clang::AS_public);
                copiedField->setDeclContext(cRecord);
                allFields.push_back(copiedField);
                addedFieldNames.insert(fieldName);
            }
        }
    }

    // 3. Include own fields
    std::vector<clang::FieldDecl*> ownFields = translateFields(cxxRecord, cRecord, disp, cppASTContext, cASTContext);
    for (auto* field : ownFields) {
        std::string fieldName = field->getNameAsString();
        if (addedFieldNames.count(fieldName) == 0) {
            allFields.push_back(field);
            addedFieldNames.insert(fieldName);
        }
    }

    // Add all fields to struct
    for (auto* field : allFields) {
        field->setDeclContext(cRecord);
        cRecord->addDecl(field);
    }

    // Complete definition
    cRecord->completeDefinition();

    llvm::outs() << "[RecordHandler] Generated base-subobject layout: " << mangledName
                 << " (" << allFields.size() << " fields)\n";

    return cRecord;
}

clang::RecordDecl* RecordHandler::generateCompleteObjectLayout(
    const clang::CXXRecordDecl* cxxRecord,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const CppToCVisitorDispatcher& disp
) {
    if (!cxxRecord) return nullptr;

    // Get mangled name (no suffix for complete object)
    std::string mangledName = cpptoc::mangle_class(cxxRecord);

    // Get source location
    clang::SourceLocation targetLoc = disp.getTargetSourceLocation(cppASTContext, cxxRecord);

    // Create identifier
    clang::IdentifierInfo& II = cASTContext.Idents.get(mangledName);

    // Create C struct (normal name)
    clang::RecordDecl* cRecord = clang::RecordDecl::Create(
        cASTContext,
        #if LLVM_VERSION_MAJOR >= 16
        clang::TagTypeKind::Struct,
        #else
        clang::TTK_Struct,
        #endif
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &II
    );

    if (!cRecord) return nullptr;

    // Start definition
    cRecord->startDefinition();

    // Analyze virtual inheritance
    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(cxxRecord);


    std::vector<clang::FieldDecl*> allFields;
    std::set<std::string> addedFieldNames;
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();

    // Collect all virtual bases (direct + indirect)
    std::set<const clang::CXXRecordDecl*> allVirtualBases;
    std::function<void(const clang::CXXRecordDecl*)> collectVirtualBases;
    collectVirtualBases = [&](const clang::CXXRecordDecl* record) {
        for (const auto& base : record->bases()) {
            if (const clang::CXXRecordDecl* baseRecord = base.getType()->getAsCXXRecordDecl()) {
                if (base.isVirtual()) {
                    allVirtualBases.insert(baseRecord->getCanonicalDecl());
                }
                collectVirtualBases(baseRecord);
            }
        }
    };
    collectVirtualBases(cxxRecord);

    // 1. Include non-virtual base fields (but not their virtual base fields)
    for (const auto& base : cxxRecord->bases()) {
        if (base.isVirtual()) continue;  // Handle virtual bases separately

        const clang::CXXRecordDecl* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        if (declMapper.hasCreated(baseRecord)) {
            // CRITICAL FIX: For non-virtual bases, use base-subobject layout (ClassName__base)
            // if the base class has virtual bases. This prevents including virtual base fields
            // that should only appear at the end of the complete-object layout.
            clang::RecordDecl* cBaseRecord = nullptr;

            if (needsDualLayout(baseRecord)) {
                // Base class has virtual bases → look for base-subobject layout (ClassName__base)
                std::string baseStructName = cpptoc::mangle_class(baseRecord) + "__base";

                // Find the base-subobject struct by name in the PathMapper TU
                // (base-subobject layouts are added to PathMapper TU in handleRecord(), not ASTContext TU)
                std::string targetPath = disp.getCurrentTargetPath();
                if (targetPath.empty()) {
                    targetPath = disp.getTargetPath(cppASTContext, cxxRecord);
                }
                cpptoc::PathMapper& pathMapper = disp.getPathMapper();
                clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);

                for (auto* decl : TU->decls()) {
                    if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
                        if (RD->getName() == baseStructName) {
                            cBaseRecord = RD;
                            break;
                        }
                    }
                }

                if (!cBaseRecord) {
                    llvm::outs() << "[RecordHandler] WARNING: Could not find base-subobject layout "
                                 << baseStructName << " for non-virtual base\n";
                    continue;
                }
            } else {
                // Base class has no virtual bases → use complete-object layout
                cBaseRecord = llvm::cast<clang::RecordDecl>(declMapper.getCreated(baseRecord));
            }

            for (auto* baseField : cBaseRecord->fields()) {
                std::string fieldName = baseField->getNameAsString();

                // Skip vbptr and duplicates
                if (fieldName == "vbptr" || addedFieldNames.count(fieldName) > 0) {
                    continue;
                }

                clang::FieldDecl* copiedField = clang::FieldDecl::Create(
                    cASTContext,
                    cRecord,
                    targetLoc,
                    targetLoc,
                    baseField->getIdentifier(),
                    baseField->getType(),
                    baseField->getTypeSourceInfo(),
                    nullptr,  // No bit width
                    false,    // Not mutable
                    clang::ICIS_NoInit
                );

                copiedField->setAccess(clang::AS_public);
                copiedField->setDeclContext(cRecord);
                allFields.push_back(copiedField);
                addedFieldNames.insert(fieldName);
            }
        }
    }

    // 2. Include own fields
    std::vector<clang::FieldDecl*> ownFields = translateFields(cxxRecord, cRecord, disp, cppASTContext, cASTContext);
    for (auto* field : ownFields) {
        std::string fieldName = field->getNameAsString();
        if (addedFieldNames.count(fieldName) == 0) {
            allFields.push_back(field);
            addedFieldNames.insert(fieldName);
        }
    }

    // 3. Include virtual base fields AT END
    for (const clang::CXXRecordDecl* vbaseRecord : allVirtualBases) {
        if (declMapper.hasCreated(vbaseRecord)) {
            clang::RecordDecl* cVbaseRecord = llvm::cast<clang::RecordDecl>(declMapper.getCreated(vbaseRecord));

            // Get the ORIGINAL C++ fields
            if (vbaseRecord->getDefinition()) {
                for (auto* originalField : vbaseRecord->fields()) {
                    std::string fieldName = originalField->getNameAsString();

                    // Skip if already added
                    if (addedFieldNames.count(fieldName) > 0) {
                        continue;
                    }

                    // Find corresponding C field in cVbaseRecord
                    clang::FieldDecl* cVbaseField = nullptr;
                    for (auto* field : cVbaseRecord->fields()) {
                        if (field->getNameAsString() == fieldName) {
                            cVbaseField = field;
                            break;
                        }
                    }

                    if (cVbaseField) {
                        clang::FieldDecl* copiedField = clang::FieldDecl::Create(
                            cASTContext,
                            cRecord,
                            targetLoc,
                            targetLoc,
                            cVbaseField->getIdentifier(),
                            cVbaseField->getType(),
                            cVbaseField->getTypeSourceInfo(),
                            nullptr,  // No bit width
                            false,    // Not mutable
                            clang::ICIS_NoInit
                        );

                        copiedField->setAccess(clang::AS_public);
                        copiedField->setDeclContext(cRecord);
                        allFields.push_back(copiedField);
                        addedFieldNames.insert(fieldName);
                    }
                }
            }
        }
    }

    // Add all fields to struct
    for (auto* field : allFields) {
        field->setDeclContext(cRecord);
        cRecord->addDecl(field);
    }

    // Complete definition
    cRecord->completeDefinition();

    llvm::outs() << "[RecordHandler] Generated complete-object layout: " << mangledName
                 << " (" << allFields.size() << " fields)\n";

    return cRecord;
}

void RecordHandler::generateImplicitC1Constructor(
    const clang::CXXRecordDecl* cxxRecord,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const CppToCVisitorDispatcher& disp
) {
    if (!cxxRecord) return;

    std::string className = cxxRecord->getNameAsString();
    std::string mangledName = cpptoc::mangle_class(cxxRecord);
    std::string c1Name = mangledName + "__ctor__void_C1";

    // Get target path and source location
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, cxxRecord);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Get or create TU
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);

    // Find the complete-object struct (ClassName)
    clang::RecordDecl* cRecordDecl = nullptr;
    for (auto* decl : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (RD->getName() == className) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        llvm::outs() << "[RecordHandler] Implicit C1: Could not find complete-object struct: "
                     << className << "\n";
        return;
    }

    // Create 'this' parameter: ClassName* (complete-object layout)
    clang::IdentifierInfo& thisII = cASTContext.Idents.get("this");
    clang::QualType classType = cASTContext.getRecordType(cRecordDecl);
    clang::QualType thisPtrType = cASTContext.getPointerType(classType);

    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cASTContext,
        TU,
        targetLoc,
        targetLoc,
        &thisII,
        thisPtrType,
        cASTContext.getTrivialTypeSourceInfo(thisPtrType),
        clang::SC_None,
        nullptr
    );

    std::vector<clang::ParmVarDecl*> allParams;
    allParams.push_back(thisParam);

    // Build constructor body
    std::vector<clang::Stmt*> bodyStmts;

    // C1: Initialize virtual bases FIRST
    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(cxxRecord);
    auto virtualBases = viAnalyzer.getVirtualBases(cxxRecord);

    for (const auto* vbase : virtualBases) {
        // Call default constructor for virtual base (use C1 if it needs dual layout)
        std::string vbaseCtorName = cpptoc::mangle_class(vbase) + "__ctor__void";
        if (needsDualLayout(vbase)) {
            vbaseCtorName += "_C1";
        }

        // Find or create virtual base constructor function declaration
        clang::FunctionDecl* vbaseCtorFunc = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
                if (FD->getNameAsString() == vbaseCtorName) {
                    vbaseCtorFunc = FD;
                    break;
                }
            }
        }

        if (!vbaseCtorFunc) {
            // Create forward declaration
            std::string vbaseStructName = vbase->getNameAsString();
            clang::RecordDecl* vbaseStruct = nullptr;
            for (auto* D : TU->decls()) {
                if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                    if (RD->getNameAsString() == vbaseStructName) {
                        vbaseStruct = RD;
                        break;
                    }
                }
            }

            if (!vbaseStruct) {
                continue; // Skip if struct not found
            }

            clang::QualType vbaseType = cASTContext.getRecordType(vbaseStruct);
            clang::QualType vbasePtrType = cASTContext.getPointerType(vbaseType);

            clang::IdentifierInfo& vbaseThisII = cASTContext.Idents.get("this");
            clang::ParmVarDecl* vbaseThisParam = clang::ParmVarDecl::Create(
                cASTContext,
                TU,
                targetLoc,
                targetLoc,
                &vbaseThisII,
                vbasePtrType,
                cASTContext.getTrivialTypeSourceInfo(vbasePtrType),
                clang::SC_None,
                nullptr
            );

            clang::IdentifierInfo& funcII = cASTContext.Idents.get(vbaseCtorName);
            vbaseCtorFunc = clang::FunctionDecl::Create(
                cASTContext,
                TU,
                targetLoc,
                targetLoc,
                clang::DeclarationName(&funcII),
                cASTContext.VoidTy,
                cASTContext.getTrivialTypeSourceInfo(cASTContext.VoidTy),
                clang::SC_None
            );

            vbaseCtorFunc->setParams({vbaseThisParam});
            TU->addDecl(vbaseCtorFunc);
        }

        // Create call: vbase_ctor((VBase*)this)
        clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
            cASTContext,
            clang::NestedNameSpecifierLoc(),
            targetLoc,
            thisParam,
            false,
            targetLoc,
            thisParam->getType(),
            clang::VK_LValue
        );

        // Cast this to virtual base pointer
        std::string vbaseStructName = vbase->getNameAsString();
        clang::RecordDecl* vbaseStruct = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                if (RD->getNameAsString() == vbaseStructName) {
                    vbaseStruct = RD;
                    break;
                }
            }
        }

        if (vbaseStruct) {
            clang::QualType vbaseType = cASTContext.getRecordType(vbaseStruct);
            clang::QualType vbasePtrType = cASTContext.getPointerType(vbaseType);

            clang::CStyleCastExpr* vbaseCast = clang::CStyleCastExpr::Create(
                cASTContext,
                vbasePtrType,
                clang::VK_PRValue,
                clang::CK_BitCast,
                thisExpr,
                nullptr,
                clang::FPOptionsOverride(),
                cASTContext.getTrivialTypeSourceInfo(vbasePtrType),
                targetLoc,
                targetLoc
            );

            clang::CallExpr* callExpr = clang::CallExpr::Create(
                cASTContext,
                clang::DeclRefExpr::Create(
                    cASTContext,
                    clang::NestedNameSpecifierLoc(),
                    targetLoc,
                    vbaseCtorFunc,
                    false,
                    targetLoc,
                    vbaseCtorFunc->getType(),
                    clang::VK_LValue
                ),
                {vbaseCast},
                cASTContext.VoidTy,
                clang::VK_PRValue,
                targetLoc,
                clang::FPOptionsOverride()
            );

            bodyStmts.push_back(callExpr);
        }
    }

    // Call non-virtual base constructors (use C2 variants if they have virtual bases)
    for (const auto& base : cxxRecord->bases()) {
        if (base.isVirtual()) continue; // Skip virtual bases (already handled)

        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        std::string baseCtorName = cpptoc::mangle_class(baseRecord) + "__ctor__void";
        if (needsDualLayout(baseRecord)) {
            baseCtorName += "_C2";
        }

        // Find or create base constructor function declaration
        clang::FunctionDecl* baseCtorFunc = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
                if (FD->getNameAsString() == baseCtorName) {
                    baseCtorFunc = FD;
                    break;
                }
            }
        }

        if (!baseCtorFunc) {
            // Create forward declaration
            std::string baseStructName = baseRecord->getNameAsString();
            if (needsDualLayout(baseRecord)) {
                baseStructName += "__base";
            }

            clang::RecordDecl* baseStruct = nullptr;
            for (auto* D : TU->decls()) {
                if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                    if (RD->getNameAsString() == baseStructName) {
                        baseStruct = RD;
                        break;
                    }
                }
            }

            if (!baseStruct) {
                continue; // Skip if struct not found
            }

            clang::QualType baseType = cASTContext.getRecordType(baseStruct);
            clang::QualType basePtrType = cASTContext.getPointerType(baseType);

            clang::IdentifierInfo& baseThisII = cASTContext.Idents.get("this");
            clang::ParmVarDecl* baseThisParam = clang::ParmVarDecl::Create(
                cASTContext,
                TU,
                targetLoc,
                targetLoc,
                &baseThisII,
                basePtrType,
                cASTContext.getTrivialTypeSourceInfo(basePtrType),
                clang::SC_None,
                nullptr
            );

            clang::IdentifierInfo& funcII = cASTContext.Idents.get(baseCtorName);
            baseCtorFunc = clang::FunctionDecl::Create(
                cASTContext,
                TU,
                targetLoc,
                targetLoc,
                clang::DeclarationName(&funcII),
                cASTContext.VoidTy,
                cASTContext.getTrivialTypeSourceInfo(cASTContext.VoidTy),
                clang::SC_None
            );

            baseCtorFunc->setParams({baseThisParam});
            TU->addDecl(baseCtorFunc);
        }

        // Create call: base_ctor((Base*)this)
        clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
            cASTContext,
            clang::NestedNameSpecifierLoc(),
            targetLoc,
            thisParam,
            false,
            targetLoc,
            thisParam->getType(),
            clang::VK_LValue
        );

        // Cast this to base pointer
        std::string baseStructName = baseRecord->getNameAsString();
        if (needsDualLayout(baseRecord)) {
            baseStructName += "__base";
        }

        clang::RecordDecl* baseStruct = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                if (RD->getNameAsString() == baseStructName) {
                    baseStruct = RD;
                    break;
                }
            }
        }

        if (baseStruct) {
            clang::QualType baseType = cASTContext.getRecordType(baseStruct);
            clang::QualType basePtrType = cASTContext.getPointerType(baseType);

            clang::CStyleCastExpr* baseCast = clang::CStyleCastExpr::Create(
                cASTContext,
                basePtrType,
                clang::VK_PRValue,
                clang::CK_BitCast,
                thisExpr,
                nullptr,
                clang::FPOptionsOverride(),
                cASTContext.getTrivialTypeSourceInfo(basePtrType),
                targetLoc,
                targetLoc
            );

            clang::CallExpr* callExpr = clang::CallExpr::Create(
                cASTContext,
                clang::DeclRefExpr::Create(
                    cASTContext,
                    clang::NestedNameSpecifierLoc(),
                    targetLoc,
                    baseCtorFunc,
                    false,
                    targetLoc,
                    baseCtorFunc->getType(),
                    clang::VK_LValue
                ),
                {baseCast},
                cASTContext.VoidTy,
                clang::VK_PRValue,
                targetLoc,
                clang::FPOptionsOverride()
            );

            bodyStmts.push_back(callExpr);
        }
    }

    // Create CompoundStmt
    clang::CompoundStmt* body = clang::CompoundStmt::Create(
        cASTContext,
        bodyStmts,
        clang::FPOptionsOverride(),
        targetLoc,
        targetLoc
    );

    // Create C function
    clang::IdentifierInfo& funcII = cASTContext.Idents.get(c1Name);
    clang::FunctionDecl* c1Func = clang::FunctionDecl::Create(
        cASTContext,
        TU,
        targetLoc,
        targetLoc,
        clang::DeclarationName(&funcII),
        cASTContext.VoidTy,
        cASTContext.getTrivialTypeSourceInfo(cASTContext.VoidTy),
        clang::SC_None
    );

    c1Func->setParams(allParams);
    c1Func->setBody(body);

    // Add to TU
    c1Func->setDeclContext(TU);
    TU->addDecl(c1Func);
    pathMapper.setNodeLocation(c1Func, targetPath);

    llvm::outs() << "[RecordHandler] Generated implicit C1 constructor: " << c1Name << "\n";
}

void RecordHandler::generateImplicitC2Constructor(
    const clang::CXXRecordDecl* cxxRecord,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const CppToCVisitorDispatcher& disp
) {
    if (!cxxRecord) return;

    std::string className = cxxRecord->getNameAsString();
    std::string mangledName = cpptoc::mangle_class(cxxRecord);
    std::string c2Name = mangledName + "__ctor__void_C2";

    // Get target path and source location
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, cxxRecord);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Get or create TU
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);

    // Find the base-subobject struct (ClassName__base)
    std::string baseStructName = className + "__base";
    clang::RecordDecl* cRecordDecl = nullptr;
    for (auto* decl : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (RD->getName() == baseStructName) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        llvm::outs() << "[RecordHandler] Implicit C2: Could not find base-subobject struct: "
                     << baseStructName << "\n";
        return;
    }

    // Create 'this' parameter: ClassName__base* (base-subobject layout)
    clang::IdentifierInfo& thisII = cASTContext.Idents.get("this");
    clang::QualType classType = cASTContext.getRecordType(cRecordDecl);
    clang::QualType thisPtrType = cASTContext.getPointerType(classType);

    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cASTContext,
        TU,
        targetLoc,
        targetLoc,
        &thisII,
        thisPtrType,
        cASTContext.getTrivialTypeSourceInfo(thisPtrType),
        clang::SC_None,
        nullptr
    );

    std::vector<clang::ParmVarDecl*> allParams;
    allParams.push_back(thisParam);

    // Build constructor body
    std::vector<clang::Stmt*> bodyStmts;

    // C2: SKIP virtual base initialization (parent's C1 handles it)

    // Call non-virtual base constructors (use C2 variants if they have virtual bases)
    for (const auto& base : cxxRecord->bases()) {
        if (base.isVirtual()) continue; // Skip virtual bases

        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (!baseRecord) continue;

        std::string baseCtorName = cpptoc::mangle_class(baseRecord) + "__ctor__void";
        if (needsDualLayout(baseRecord)) {
            baseCtorName += "_C2";
        }

        // Find or create base constructor function declaration
        clang::FunctionDecl* baseCtorFunc = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
                if (FD->getNameAsString() == baseCtorName) {
                    baseCtorFunc = FD;
                    break;
                }
            }
        }

        if (!baseCtorFunc) {
            // Create forward declaration
            std::string baseStructName = baseRecord->getNameAsString();
            if (needsDualLayout(baseRecord)) {
                baseStructName += "__base";
            }

            clang::RecordDecl* baseStruct = nullptr;
            for (auto* D : TU->decls()) {
                if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                    if (RD->getNameAsString() == baseStructName) {
                        baseStruct = RD;
                        break;
                    }
                }
            }

            if (!baseStruct) {
                continue; // Skip if struct not found
            }

            clang::QualType baseType = cASTContext.getRecordType(baseStruct);
            clang::QualType basePtrType = cASTContext.getPointerType(baseType);

            clang::IdentifierInfo& baseThisII = cASTContext.Idents.get("this");
            clang::ParmVarDecl* baseThisParam = clang::ParmVarDecl::Create(
                cASTContext,
                TU,
                targetLoc,
                targetLoc,
                &baseThisII,
                basePtrType,
                cASTContext.getTrivialTypeSourceInfo(basePtrType),
                clang::SC_None,
                nullptr
            );

            clang::IdentifierInfo& funcII = cASTContext.Idents.get(baseCtorName);
            baseCtorFunc = clang::FunctionDecl::Create(
                cASTContext,
                TU,
                targetLoc,
                targetLoc,
                clang::DeclarationName(&funcII),
                cASTContext.VoidTy,
                cASTContext.getTrivialTypeSourceInfo(cASTContext.VoidTy),
                clang::SC_None
            );

            baseCtorFunc->setParams({baseThisParam});
            TU->addDecl(baseCtorFunc);
        }

        // Create call: base_ctor((Base*)this)
        clang::DeclRefExpr* thisExpr = clang::DeclRefExpr::Create(
            cASTContext,
            clang::NestedNameSpecifierLoc(),
            targetLoc,
            thisParam,
            false,
            targetLoc,
            thisParam->getType(),
            clang::VK_LValue
        );

        // Cast this to base pointer
        std::string baseStructName = baseRecord->getNameAsString();
        if (needsDualLayout(baseRecord)) {
            baseStructName += "__base";
        }

        clang::RecordDecl* baseStruct = nullptr;
        for (auto* D : TU->decls()) {
            if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                if (RD->getNameAsString() == baseStructName) {
                    baseStruct = RD;
                    break;
                }
            }
        }

        if (baseStruct) {
            clang::QualType baseType = cASTContext.getRecordType(baseStruct);
            clang::QualType basePtrType = cASTContext.getPointerType(baseType);

            clang::CStyleCastExpr* baseCast = clang::CStyleCastExpr::Create(
                cASTContext,
                basePtrType,
                clang::VK_PRValue,
                clang::CK_BitCast,
                thisExpr,
                nullptr,
                clang::FPOptionsOverride(),
                cASTContext.getTrivialTypeSourceInfo(basePtrType),
                targetLoc,
                targetLoc
            );

            clang::CallExpr* callExpr = clang::CallExpr::Create(
                cASTContext,
                clang::DeclRefExpr::Create(
                    cASTContext,
                    clang::NestedNameSpecifierLoc(),
                    targetLoc,
                    baseCtorFunc,
                    false,
                    targetLoc,
                    baseCtorFunc->getType(),
                    clang::VK_LValue
                ),
                {baseCast},
                cASTContext.VoidTy,
                clang::VK_PRValue,
                targetLoc,
                clang::FPOptionsOverride()
            );

            bodyStmts.push_back(callExpr);
        }
    }

    // Create CompoundStmt
    clang::CompoundStmt* body = clang::CompoundStmt::Create(
        cASTContext,
        bodyStmts,
        clang::FPOptionsOverride(),
        targetLoc,
        targetLoc
    );

    // Create C function
    clang::IdentifierInfo& funcII = cASTContext.Idents.get(c2Name);
    clang::FunctionDecl* c2Func = clang::FunctionDecl::Create(
        cASTContext,
        TU,
        targetLoc,
        targetLoc,
        clang::DeclarationName(&funcII),
        cASTContext.VoidTy,
        cASTContext.getTrivialTypeSourceInfo(cASTContext.VoidTy),
        clang::SC_None
    );

    c2Func->setParams(allParams);
    c2Func->setBody(body);

    // Add to TU
    c2Func->setDeclContext(TU);
    TU->addDecl(c2Func);
    pathMapper.setNodeLocation(c2Func, targetPath);

    llvm::outs() << "[RecordHandler] Generated implicit C2 constructor: " << c2Name << "\n";
}

// Phase 4: Migrated to NameMangler free function API (mangle_class)
// Free functions provide unified name mangling for all declarations (classes, methods, functions)
// and handle both namespaces (single _) and nested structs (double __) correctly
// Benefits: no instantiation overhead, no const_cast needed, cleaner code

} // namespace cpptoc
