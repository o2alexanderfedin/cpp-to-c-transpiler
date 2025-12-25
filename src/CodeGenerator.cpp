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
    Policy.IncludeTagDefinition = false;  // DON'T expand struct definitions in types (Phase 28 fix)
    Policy.Indentation = 4;  // 4-space indentation (standard C style)

    // DRY: Reuse Clang's well-tested policy defaults for everything else
    return Policy;
}

// Print a declaration using Clang's DeclPrinter
// Dependency Inversion: Depends on Clang's abstract Decl interface
// Phase 35-02: Fixed to convert C++ references to C pointers in all function declarations
void CodeGenerator::printDecl(Decl *D, bool declarationOnly) {
    if (!D) return;

    if (auto *FD = dyn_cast<FunctionDecl>(D)) {
        if (declarationOnly) {
            // Print function signature only (for header)
            printFunctionSignature(FD);
            OS << ";\n";
        } else {
            // Phase 35-02: Print full function with C-compatible signature
            // We need to print the signature ourselves to convert references to pointers
            printFunctionSignature(FD);

            // Print function body if present
            if (FD->hasBody()) {
                OS << " ";
                printStmt(FD->getBody(), 0);
            } else {
                OS << ";";
            }
            OS << "\n";
        }
    } else if (isa<RecordDecl>(D) || isa<EnumDecl>(D)) {
        // Struct/enum definitions should only be in header files
        // Skip them when generating implementation files to avoid redefinition errors
        if (declarationOnly) {
            D->print(OS, Policy);
            OS << ";\n";
        }
        // When declarationOnly=false (implementation file), skip struct/enum definitions
        // They are already in the header file
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

// Phase 35-02: Convert C++ QualType to C-compatible type (references -> pointers)
// CRITICAL BUG FIX: C++ references must be converted to C pointers
QualType CodeGenerator::convertToCType(QualType Type) {
    // Strip top-level const/volatile qualifiers temporarily
    bool isConst = Type.isConstQualified();
    bool isVolatile = Type.isVolatileQualified();

    // Get the underlying type without qualifiers
    QualType BaseType = Type.getUnqualifiedType();
    const clang::Type *TypePtr = BaseType.getTypePtr();

    // Check if it's a reference type (lvalue or rvalue)
    if (const ReferenceType *RefType = dyn_cast<ReferenceType>(TypePtr)) {
        // Get the pointee type (what the reference refers to)
        QualType PointeeType = RefType->getPointeeType();

        // References become pointers in C
        // Note: Const qualifier from the reference type needs to be preserved
        // Example: const T& → const T*
        QualType PointerType = Context.getPointerType(PointeeType);

        // Re-apply const/volatile if they were on the reference
        if (isConst) {
            PointerType = Context.getConstType(PointerType);
        }
        if (isVolatile) {
            PointerType = Context.getVolatileType(PointerType);
        }

        return PointerType;
    }

    // Not a reference - return original type
    return Type;
}

// Phase 35-03: Print type with 'struct' prefix for class/struct types
// CRITICAL BUG FIX: Return types for class/struct need 'struct' prefix in C
void CodeGenerator::printCType(QualType Type) {
    // Extract const/volatile qualifiers
    bool isConst = Type.isConstQualified();
    bool isVolatile = Type.isVolatileQualified();

    // Print qualifiers first
    if (isConst) {
        OS << "const ";
    }
    if (isVolatile) {
        OS << "volatile ";
    }

    // Get the base type without qualifiers
    QualType BaseType = Type.getUnqualifiedType();
    const clang::Type *TypePtr = BaseType.getTypePtr();

    // Handle pointer types - need to recurse for pointee type
    if (const PointerType *PT = dyn_cast<PointerType>(TypePtr)) {
        QualType PointeeType = PT->getPointeeType();

        // Special handling: if pointee is a record type, print "struct" before recursing
        // This handles cases like: Vector3D* -> struct Vector3D *
        QualType UnqualifiedPointee = PointeeType.getUnqualifiedType();
        const clang::Type *PointeePtr = UnqualifiedPointee.getTypePtr();

        // Check canonical type to handle ElaboratedType
        const clang::Type *CanonicalPointeePtr = UnqualifiedPointee.getCanonicalType().getTypePtr();

        if (const RecordType *RT = dyn_cast<RecordType>(CanonicalPointeePtr)) {
            // Pointee is a class/struct - print qualifiers + struct + name + *
            if (PointeeType.isConstQualified()) {
                OS << "const ";
            }
            if (PointeeType.isVolatileQualified()) {
                OS << "volatile ";
            }

            RecordDecl *RD = RT->getDecl();
            OS << "struct " << RD->getNameAsString() << " *";
            return;
        }

        // Also check direct RecordType (without elaboration)
        if (const RecordType *RT = dyn_cast<RecordType>(PointeePtr)) {
            // Pointee is a class/struct - print qualifiers + struct + name + *
            if (PointeeType.isConstQualified()) {
                OS << "const ";
            }
            if (PointeeType.isVolatileQualified()) {
                OS << "volatile ";
            }

            RecordDecl *RD = RT->getDecl();
            OS << "struct " << RD->getNameAsString() << " *";
            return;
        }

        // Regular pointer - print pointee type + *
        printCType(PointeeType);
        OS << " *";
        return;
    }

    // Handle record types (class/struct) - add 'struct' prefix
    // Note: May be wrapped in ElaboratedType, so we need to check the canonical type
    const clang::Type *CanonicalTypePtr = BaseType.getCanonicalType().getTypePtr();
    if (const RecordType *RT = dyn_cast<RecordType>(CanonicalTypePtr)) {
        RecordDecl *RD = RT->getDecl();
        OS << "struct " << RD->getNameAsString();
        return;
    }

    // Also check if it's directly a RecordType (without elaboration)
    if (const RecordType *RT = dyn_cast<RecordType>(TypePtr)) {
        RecordDecl *RD = RT->getDecl();
        OS << "struct " << RD->getNameAsString();
        return;
    }

    // For all other types (primitives, etc.), use default printing
    BaseType.print(OS, Policy);
}

// Phase 28: Print function signature without body (for header files)
// Phase 35-02: Fixed to convert C++ references to C pointers
// Phase 35-03: Fixed to add 'struct' prefix for class/struct return types
void CodeGenerator::printFunctionSignature(FunctionDecl *FD) {
    if (!FD) return;

    // Bug #19: Print storage class specifier (static/extern) before return type
    if (FD->getStorageClass() == SC_Static) {
        OS << "static ";
    } else if (FD->getStorageClass() == SC_Extern) {
        OS << "extern ";
    }

    // Return type - convert references to pointers and add 'struct' prefix
    QualType ReturnType = convertToCType(FD->getReturnType());
    printCType(ReturnType);
    OS << " ";

    // Function name
    OS << FD->getNameAsString();

    // Parameters
    OS << "(";
    for (unsigned i = 0; i < FD->getNumParams(); ++i) {
        if (i > 0) OS << ", ";
        ParmVarDecl *Param = FD->getParamDecl(i);

        // Phase 35-02: Convert C++ reference parameters to C pointers
        // Phase 35-03: Add 'struct' prefix for class/struct parameters
        QualType ParamType = convertToCType(Param->getType());
        printCType(ParamType);

        if (!Param->getNameAsString().empty()) {
            OS << " " << Param->getNameAsString();
        }
    }
    OS << ")";
}
