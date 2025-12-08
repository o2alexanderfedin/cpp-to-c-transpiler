// Story #21: DeclPrinter/StmtPrinter Integration - Implementation
// SOLID: Single responsibility - code generation
// KISS: Use Clang's built-in printers (DRY - don't reimplement)

#include "CodeGenerator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/ASTContext.h"

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
    C99Opts.C23 = 0;

    // Disable ALL C++ features
    // YAGNI: Only what we need for C99
    C99Opts.CPlusPlus = 0;
    C99Opts.CPlusPlus11 = 0;
    C99Opts.CPlusPlus14 = 0;
    C99Opts.CPlusPlus17 = 0;
    C99Opts.CPlusPlus20 = 0;
    C99Opts.CPlusPlus23 = 0;
    C99Opts.CPlusPlus26 = 0;

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
void CodeGenerator::printDecl(Decl *D) {
    if (!D) return;

    // Use Clang's built-in DeclPrinter (via Decl::print)
    // KISS: Don't reinvent the wheel - Clang's printer is battle-tested
    D->print(OS, Policy);

    // C requires semicolon after struct/typedef declarations
    // Check if this is a tag declaration (struct/union/enum)
    if (isa<RecordDecl>(D) || isa<EnumDecl>(D)) {
        OS << ";";
    }

    OS << "\n";
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
