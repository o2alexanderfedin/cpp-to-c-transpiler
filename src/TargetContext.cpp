#include "TargetContext.h"
#include "clang/Basic/DiagnosticIDs.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Basic/FileSystemOptions.h"
#include "llvm/Config/llvm-config.h" // For LLVM_VERSION_MAJOR

// LLVM 16+ moved Host.h to TargetParser subdirectory
#if LLVM_VERSION_MAJOR >= 16
#include "llvm/TargetParser/Host.h"
#else
#include "llvm/Support/Host.h"
#endif

#include "llvm/Support/raw_ostream.h"

TargetContext::TargetContext() {
    llvm::outs() << "[Bug #30 FIX] Creating independent target ASTContext for C output...\n";

    // 1. Create FileManager
    clang::FileSystemOptions FileSystemOpts;
    FileMgr = std::make_unique<clang::FileManager>(FileSystemOpts);

    // 2. Create DiagnosticsEngine with diagnostic options
    // Bug #31 FIX: Store DiagClient in unique_ptr to ensure proper cleanup
    // CRITICAL: Pass ShouldOwnClient=false to prevent double-free
    // TargetContext owns DiagClient, not DiagnosticsEngine
    clang::IntrusiveRefCntPtr<clang::DiagnosticIDs> DiagID(new clang::DiagnosticIDs());
    DiagOpts = std::make_unique<clang::DiagnosticOptions>();
    DiagClient = std::make_unique<clang::IgnoringDiagConsumer>();

    // API change: LLVM 15 uses IntrusiveRefCntPtr, LLVM 16+ uses reference
    #if LLVM_VERSION_MAJOR >= 16
    Diagnostics = std::make_unique<clang::DiagnosticsEngine>(
        DiagID, *DiagOpts, DiagClient.get(), /* ShouldOwnClient */ false);
    #else
    // LLVM 15: DiagnosticsEngine expects IntrusiveRefCntPtr for DiagnosticOptions
    clang::IntrusiveRefCntPtr<clang::DiagnosticOptions> DiagOptsPtr(DiagOpts.get());
    Diagnostics = std::make_unique<clang::DiagnosticsEngine>(
        DiagID, DiagOptsPtr, DiagClient.get(), /* ShouldOwnClient */ false);
    #endif

    // 3. Create SourceManager
    SourceMgr = std::make_unique<clang::SourceManager>(*Diagnostics, *FileMgr);

    // 4. Create TargetInfo (use host triple for C output)
    std::string TargetTriple = llvm::sys::getDefaultTargetTriple();
    TargetOpts = std::make_unique<clang::TargetOptions>();
    TargetOpts->Triple = TargetTriple;

    // API change: LLVM 15 uses shared_ptr, LLVM 16+ uses reference
    #if LLVM_VERSION_MAJOR >= 16
    Target.reset(clang::TargetInfo::CreateTargetInfo(*Diagnostics, *TargetOpts));
    #else
    // LLVM 15: CreateTargetInfo expects shared_ptr, takes ownership
    std::shared_ptr<clang::TargetOptions> SharedTargetOpts(TargetOpts.release());
    Target.reset(clang::TargetInfo::CreateTargetInfo(*Diagnostics, SharedTargetOpts));
    // Note: SharedTargetOpts now owns the TargetOptions, TargetOpts is null
    #endif

    // 5. Create LangOptions for C11
    clang::LangOptions LangOpts;
    LangOpts.C11 = 1;
    LangOpts.Bool = 1;       // Enable _Bool type
    LangOpts.Digraphs = 1;
    LangOpts.LineComment = 1;

    // 6. Create IdentifierTable
    Idents = std::make_unique<clang::IdentifierTable>(LangOpts);

    // 7. Create SelectorTable
    Selectors = std::make_unique<clang::SelectorTable>();

    // 8. Create Builtin::Context and initialize with Target
    Builtins = std::make_unique<clang::Builtin::Context>();

    // Bug #32 FIX: Initialize builtins with target BEFORE creating ASTContext
    // This ensures ASTContext has access to target-specific type information
    Builtins->InitializeTarget(*Target, /* AuxTarget */ nullptr);

    // 9. Create the target ASTContext
    // Note: ASTContext will use the Target from Builtins for type information
    Context = std::make_unique<clang::ASTContext>(
        LangOpts,
        *SourceMgr,
        *Idents,
        *Selectors,
        *Builtins,
        clang::TranslationUnitKind::TU_Complete
    );

    // Bug #32 FIX: Initialize builtin types with target information
    // CRITICAL: This sets IntTy, VoidTy, BoolTy, etc. based on TargetInfo
    // Without this, accessing Ctx.IntTy will crash!
    Context->InitBuiltinTypes(*Target, /* AuxTarget */ nullptr);

    llvm::outs() << "[Bug #30 FIX] Target ASTContext created successfully:\n";
    llvm::outs() << "  - ASTContext @ " << (void*)Context.get() << "\n";
    llvm::outs() << "  - Target Triple: " << TargetTriple << "\n";
    llvm::outs() << "  - Language: C11\n";
}

TargetContext::~TargetContext() {
    // Bug #31 FIX: Explicitly destroy Context and Diagnostics before other dependencies
    // Order of destruction must be:
    // 1. Context (may access SourceManager, etc.)
    // 2. Diagnostics (may access DiagClient)
    // 3. DiagClient (must outlive Diagnostics)
    // 4. Other members (SourceMgr, FileMgr, etc.)

    // Bug #32 FIX: Add defensive checks to prevent double-free or null-pointer issues
    try {
        // Destroy Context first
        if (Context) {
            Context.reset();
        }

        // Destroy Diagnostics second
        if (Diagnostics) {
            Diagnostics.reset();
        }
    } catch (...) {
        // Silently catch any exceptions during cleanup to prevent crashes
        // Destructor should never throw
    }

    // Other members will be destroyed automatically in reverse declaration order:
    // Builtins, Selectors, Idents, Target, SourceMgr, FileMgr, DiagClient
}

// Phase 1.1: Node tracking and deduplication methods

clang::EnumDecl* TargetContext::findEnum(const std::string& name) {
    auto it = globalEnums.find(name);
    if (it != globalEnums.end()) {
        return it->second;
    }
    return nullptr;
}

clang::RecordDecl* TargetContext::findStruct(const std::string& name) {
    auto it = globalStructs.find(name);
    if (it != globalStructs.end()) {
        return it->second;
    }
    return nullptr;
}

clang::TypedefDecl* TargetContext::findTypedef(const std::string& name) {
    auto it = globalTypedefs.find(name);
    if (it != globalTypedefs.end()) {
        return it->second;
    }
    return nullptr;
}

void TargetContext::recordNode(const clang::Decl* node, const std::string& location) {
    if (!node) return;

    nodeToLocation[node] = location;

    // Also record in type-specific maps for deduplication
    if (auto enumDecl = llvm::dyn_cast<clang::EnumDecl>(node)) {
        std::string name = enumDecl->getNameAsString();
        if (!name.empty()) {
            globalEnums[name] = const_cast<clang::EnumDecl*>(enumDecl);
        }
    } else if (auto recordDecl = llvm::dyn_cast<clang::RecordDecl>(node)) {
        std::string name = recordDecl->getNameAsString();
        if (!name.empty()) {
            globalStructs[name] = const_cast<clang::RecordDecl*>(recordDecl);
        }
    } else if (auto typedefDecl = llvm::dyn_cast<clang::TypedefDecl>(node)) {
        std::string name = typedefDecl->getNameAsString();
        if (!name.empty()) {
            globalTypedefs[name] = const_cast<clang::TypedefDecl*>(typedefDecl);
        }
    }
}

std::string TargetContext::getLocation(const clang::Decl* node) const {
    if (!node) return "";

    auto it = nodeToLocation.find(node);
    if (it != nodeToLocation.end()) {
        return it->second;
    }
    return "";
}
