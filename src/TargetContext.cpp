#include "TargetContext.h"
#include "clang/Basic/DiagnosticIDs.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Basic/FileSystemOptions.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/Support/raw_ostream.h"

// Initialize static instance
TargetContext* TargetContext::instance = nullptr;

TargetContext::TargetContext() {
    llvm::outs() << "[Bug #30 FIX] Creating independent target ASTContext for C output...\n";

    // 1. Create FileManager
    clang::FileSystemOptions FileSystemOpts;
    FileMgr = std::make_unique<clang::FileManager>(FileSystemOpts);

    // 2. Create DiagnosticsEngine with diagnostic options
    // Bug #31 FIX: Store DiagClient in unique_ptr to ensure proper cleanup
    clang::IntrusiveRefCntPtr<clang::DiagnosticIDs> DiagID(new clang::DiagnosticIDs());
    auto DiagOpts = std::make_unique<clang::DiagnosticOptions>();
    DiagClient = std::make_unique<clang::IgnoringDiagConsumer>();
    Diagnostics = std::make_unique<clang::DiagnosticsEngine>(
        DiagID, *DiagOpts, DiagClient.get());

    // 3. Create SourceManager
    SourceMgr = std::make_unique<clang::SourceManager>(*Diagnostics, *FileMgr);

    // 4. Create TargetInfo (use host triple for C output)
    std::string TargetTriple = llvm::sys::getDefaultTargetTriple();
    auto TargetOpts = std::make_shared<clang::TargetOptions>();
    TargetOpts->Triple = TargetTriple;
    Target.reset(clang::TargetInfo::CreateTargetInfo(*Diagnostics, *TargetOpts));

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

TargetContext& TargetContext::getInstance() {
    if (!instance) {
        instance = new TargetContext();
    }
    return *instance;
}

void TargetContext::cleanup() {
    // Bug #31 FIX: Clean up singleton before program exit
    // This is called via atexit handler to ensure proper cleanup order
    if (instance) {
        delete instance;
        instance = nullptr;
    }
}
