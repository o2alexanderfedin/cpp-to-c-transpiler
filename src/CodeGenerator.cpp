// Story #21: DeclPrinter/StmtPrinter Integration - Implementation
// SOLID: Single responsibility - code generation
// KISS: Use Clang's built-in printers (DRY - don't reimplement)

#include "CodeGenerator.h"
#include "llvm/Config/llvm-config.h"  // For LLVM_VERSION_MAJOR
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/ASTContext.h"
#include "clang/Basic/SourceManager.h"  // Story #23: For #line directives

using namespace clang;
using namespace llvm;

// Constructor: Initialize with output stream and context
// Story #22: Configure PrintingPolicy for C99 output
CodeGenerator::CodeGenerator(raw_ostream &OS, ASTContext &Ctx)
    : OS(OS), Policy(createC99Policy(Ctx)), Context(Ctx) {
    // Policy created via createC99Policy() helper
}

// Story #22: Create C99-compliant PrintingPolicy
// SOLID: Single function responsible for policy configuration
// KISS: Configure only what's needed for C99, use defaults for rest
PrintingPolicy CodeGenerator::createC99Policy(ASTContext &Ctx) {
    // Create LangOptions for C99
    LangOptions C99Opts;

    // Enable C99 mode
    C99Opts.C99 = 1;
    C99Opts.C11 = 0;
    C99Opts.C17 = 0;
#if LLVM_VERSION_MAJOR >= 16
    C99Opts.C23 = 0;
#else
    // LLVM 15 uses C2x instead of C23
    C99Opts.C2x = 0;
#endif

    // Disable ALL C++ features
    // YAGNI: Only what we need for C99
    C99Opts.CPlusPlus = 0;
    C99Opts.CPlusPlus11 = 0;
    C99Opts.CPlusPlus14 = 0;
    C99Opts.CPlusPlus17 = 0;
    C99Opts.CPlusPlus20 = 0;
#if LLVM_VERSION_MAJOR >= 16
    C99Opts.CPlusPlus23 = 0;
    C99Opts.CPlusPlus26 = 0;
#endif

    // Disable C++ specific features
    C99Opts.Exceptions = 0;
    C99Opts.CXXExceptions = 0;
    C99Opts.RTTI = 0;

    // Create PrintingPolicy with C99 LangOptions
    PrintingPolicy Policy(C99Opts);

    // Configure bool type (use _Bool in C99, not bool)
    Policy.Bool = true;  // Print _Bool instead of bool

    // Formatting preferences for readable C code
    Policy.SuppressTagKeyword = false;  // Keep 'struct' keyword
    Policy.SuppressSpecifiers = false;  // Keep type specifiers
    Policy.IncludeTagDefinition = true;  // Print full struct definitions
    Policy.Indentation = 4;  // 4-space indentation (standard C style)

    // DRY: Reuse Clang's well-tested policy defaults for everything else
    return Policy;
}

// Print a declaration using Clang's DeclPrinter
// Dependency Inversion: Depends on Clang's abstract Decl interface
void CodeGenerator::printDecl(Decl *D, bool declarationOnly) {
    if (!D) return;

    if (auto *FD = dyn_cast<FunctionDecl>(D)) {
        if (declarationOnly) {
            // Print function signature only (for header)
            printFunctionSignature(FD);
            OS << ";\n";
        } else {
            // Print full function (for implementation)
            // Use Clang's built-in DeclPrinter (via Decl::print)
            D->print(OS, Policy);
            OS << "\n";
        }
    } else if (isa<RecordDecl>(D) || isa<EnumDecl>(D)) {
        // Struct/enum definitions always complete (same for header and impl)
        D->print(OS, Policy);
        OS << ";\n";
    } else {
        // Other declarations
        D->print(OS, Policy);

        // C requires semicolon after certain declarations
        if (isa<RecordDecl>(D) || isa<EnumDecl>(D)) {
            OS << ";";
        } else if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            // Function declarations without bodies need semicolon
            if (!FD->hasBody()) {
                OS << ";";
            }
        }
        OS << "\n";
    }
}

// Print a statement using Clang's StmtPrinter
// Uses Stmt::printPretty() for clean formatting
void CodeGenerator::printStmt(Stmt *S, unsigned Indent) {
    if (!S) return;

    // Use Clang's built-in StmtPrinter (via Stmt::printPretty)
    // KISS: Leverage existing, tested infrastructure
    S->printPretty(OS, nullptr, Policy, Indent);
    OS << "\n";
}

// Story #23: Print declaration with #line directive for source mapping
// Maps generated C code back to original C++ source for debugging
void CodeGenerator::printDeclWithLineDirective(Decl *D) {
    if (!D) return;

    // Get source location
    SourceLocation Loc = D->getLocation();

    // Only inject #line if location is valid
    if (Loc.isValid()) {
        SourceManager &SM = Context.getSourceManager();
        PresumedLoc PLoc = SM.getPresumedLoc(Loc);

        // Check if PresumedLoc is valid (handles macro expansions, etc.)
        if (PLoc.isValid()) {
            // Inject #line directive
            // Format: #line <line_number> "<filename>"
            OS << "#line " << PLoc.getLine()
               << " \"" << PLoc.getFilename() << "\"\n";
        }
    }

    // Print the declaration (with or without #line)
    printDecl(D);
}

// Print entire translation unit
// Skips implicit declarations (compiler-generated cruft)
void CodeGenerator::printTranslationUnit(TranslationUnitDecl *TU) {
    if (!TU) return;

    // Iterate through all declarations in TU
    for (Decl *D : TU->decls()) {
        // Skip implicit declarations (e.g., built-in types)
        // YAGNI: Only print what we actually need
        if (!D->isImplicit()) {
            printDecl(D);
        }
    }
}

// Story #23: Print translation unit with #line directives
void CodeGenerator::printTranslationUnitWithLineDirectives(TranslationUnitDecl *TU) {
    if (!TU) return;

    for (Decl *D : TU->decls()) {
        if (!D->isImplicit()) {
            printDeclWithLineDirective(D);
        }
    }
}

// Phase 28: Print function signature without body (for header files)
void CodeGenerator::printFunctionSignature(FunctionDecl *FD) {
    if (!FD) return;

    // Return type
    FD->getReturnType().print(OS, Policy);
    OS << " ";

    // Function name
    OS << FD->getNameAsString();

    // Parameters
    OS << "(";
    for (unsigned i = 0; i < FD->getNumParams(); ++i) {
        if (i > 0) OS << ", ";
        ParmVarDecl *Param = FD->getParamDecl(i);

        // Create a copy of the policy with SuppressTagKeyword disabled
        // This prevents printing full struct definitions in parameter types
        PrintingPolicy ParamPolicy = Policy;
        ParamPolicy.IncludeTagDefinition = false;  // Don't include full struct definition

        Param->getType().print(OS, ParamPolicy);
        if (!Param->getNameAsString().empty()) {
            OS << " " << Param->getNameAsString();
        }
    }
    OS << ")";
}
