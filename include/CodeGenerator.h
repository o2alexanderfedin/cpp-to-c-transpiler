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

    // Phase 35-03: Print type with proper 'struct' prefix for class/struct types
    /// @brief Print type with 'struct' prefix for record types
    /// @param Type Type to print (after convertToCType)
    /// CRITICAL BUG FIX: Adds 'struct' prefix for class/struct types in C
    void printCType(clang::QualType Type);

    // Bug #21: Check if expression contains RecoveryExpr
    /// @brief Recursively check if expression contains RecoveryExpr
    /// @param E Expression to check
    /// @return true if E or any child contains RecoveryExpr
    /// BUG FIX: Prevents literal "<recovery-expr>()" from appearing in generated C code
    bool containsRecoveryExpr(clang::Expr *E);

    // Phase 47 Group 1 Task 2: Typedef generation decision logic
    /// @brief Determine if enum should use typedef (C99) or inline type (C23)
    /// @param ED Enum declaration to check
    /// @return true if typedef should be used (always true for C99 compatibility)
    /// @note C99 approach: ALWAYS use typedef for maximum compatibility
    /// @note C23 approach (future): Could use inline enum Name : Type { ... }
    /// @note Current implementation: C99 (typedef for all enums)
    bool shouldUseTypedef(clang::EnumDecl *ED) const {
        // C99 compatibility: Always use typedef for all enums
        // This ensures the enum type name can be used without "enum" prefix
        // Example: typedef enum { Red, Green } Color; allows "Color c;" instead of "enum Color c;"
        (void)ED; // Unused in C99 mode
        return true;
    }

    // Bug #23: Print enum as typedef enum for C compatibility
    /// @brief Print enum declaration as C typedef enum
    /// @param ED Enum declaration to print
    /// BUG FIX: Prints "typedef enum { ... } Name;" instead of "enum Name : int { ... };"
    /// PHASE 47: Uses shouldUseTypedef() to determine typedef vs inline (always typedef in C99)
    void printEnumDecl(clang::EnumDecl *ED);

    // Bug #24: Print struct with 'struct' prefixes for field types
    /// @brief Print struct declaration with 'struct' prefixes for field types
    /// @param RD Record declaration to print
    /// BUG FIX #24: Prints "struct Foo { struct Bar *field; }" instead of "struct Foo { Bar *field; }"
    void printStructDecl(clang::RecordDecl *RD);

    // Bug #37: Print expression with C-compatible syntax (no C++ qualifiers)
    /// @brief Print expression with C syntax (converts C++ :: to C naming)
    /// @param E Expression to print
    /// BUG FIX #37: Converts GameState::Menu to Menu (just the enum constant name)
    /// BUG FIX #40: Converts obj.method() to ClassName_method(&obj)
    /// BUG FIX #41: Converts Class::staticMethod() to Class_staticMethod()
    void printExpr(clang::Expr *E);
};
