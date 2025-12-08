#pragma once

// Story #21: DeclPrinter/StmtPrinter Integration
// Single Responsibility: Generate C code from AST #2 using Clang's printers

#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/PrettyPrinter.h"
#include "llvm/Support/raw_ostream.h"

// CodeGenerator: Generate clean C code from C AST using Clang's DeclPrinter/StmtPrinter
// SOLID: Single responsibility - code generation only
// KISS: Leverage Clang's battle-tested printers, don't reinvent the wheel
class CodeGenerator {
    llvm::raw_ostream &OS;
    clang::PrintingPolicy Policy;
    clang::ASTContext &Context;

public:
    // Constructor: Initialize with output stream and ASTContext
    // PrintingPolicy will be configured in Story #22
    explicit CodeGenerator(llvm::raw_ostream &OS, clang::ASTContext &Ctx);

    // Print a single declaration (struct, function, variable)
    // Uses Decl::print() internally
    void printDecl(clang::Decl *D);

    // Print a single statement (if, while, return, etc.)
    // Uses Stmt::printPretty() internally
    void printStmt(clang::Stmt *S, unsigned Indent = 0);

    // Print an entire translation unit (all declarations)
    // Skips implicit declarations (compiler-generated)
    void printTranslationUnit(clang::TranslationUnitDecl *TU);

    // Access printing policy (for testing)
    clang::PrintingPolicy& getPrintingPolicy() { return Policy; }

private:
    // Story #22: Create C99-compliant PrintingPolicy
    static clang::PrintingPolicy createC99Policy(clang::ASTContext &Ctx);
};
