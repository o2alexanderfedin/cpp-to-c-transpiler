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
    // Phase 28: Added declarationOnly parameter for header/impl separation
    /// @param D Declaration to print
    /// @param declarationOnly If true, print signature only (for .h files)
    void printDecl(clang::Decl *D, bool declarationOnly = false);

    // Story #23: Print declaration with #line directive for source mapping
    void printDeclWithLineDirective(clang::Decl *D);

    // Print a single statement (if, while, return, etc.)
    // Uses Stmt::printPretty() internally
    void printStmt(clang::Stmt *S, unsigned Indent = 0);

    // Print an entire translation unit (all declarations)
    // Skips implicit declarations (compiler-generated)
    void printTranslationUnit(clang::TranslationUnitDecl *TU);

    // Story #23: Print translation unit with #line directives
    void printTranslationUnitWithLineDirectives(clang::TranslationUnitDecl *TU);

    // Access printing policy (for testing)
    clang::PrintingPolicy& getPrintingPolicy() { return Policy; }

private:
    // Story #22: Create C99-compliant PrintingPolicy
    static clang::PrintingPolicy createC99Policy(clang::ASTContext &Ctx);

    // Phase 28: Print function signature without body (for header files)
    /// @brief Print function signature without body
    /// @param FD Function declaration
    void printFunctionSignature(clang::FunctionDecl *FD);

    // Phase 35-02: Convert C++ types to C types (references -> pointers)
    /// @brief Convert C++ QualType to C-compatible type
    /// @param Type C++ type (may contain references)
    /// @return C type (references converted to pointers)
    /// CRITICAL BUG FIX: Converts C++ references (&, &&) to C pointers (*)
    clang::QualType convertToCType(clang::QualType Type);
};
