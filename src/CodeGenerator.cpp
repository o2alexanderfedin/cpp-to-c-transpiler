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
// Story #22 will enhance PrintingPolicy for C99
CodeGenerator::CodeGenerator(raw_ostream &OS, ASTContext &Ctx)
    : OS(OS), Policy(Ctx.getLangOpts()), Context(Ctx) {
    // Basic policy configuration
    // Story #22 will add full C99 configuration
}

// Print a declaration using Clang's DeclPrinter
// Dependency Inversion: Depends on Clang's abstract Decl interface
void CodeGenerator::printDecl(Decl *D) {
    if (!D) return;

    // Use Clang's built-in DeclPrinter (via Decl::print)
    // KISS: Don't reinvent the wheel - Clang's printer is battle-tested
    D->print(OS, Policy);
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
