// Story #21: DeclPrinter/StmtPrinter Integration - Implementation
// SOLID: Single responsibility - code generation
// KISS: Use Clang's built-in printers (DRY - don't reimplement)

#include "CodeGenerator.h"
#include "llvm/Config/llvm-config.h"  // For LLVM_VERSION_MAJOR
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"  // For CXXMethodDecl
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"  // For ForStmt
#include "clang/AST/Expr.h"  // Bug #21: For Expr and RecoveryExpr
#include "clang/AST/ExprCXX.h"  // For CXXMemberCallExpr
#include "clang/AST/ASTContext.h"
#include "clang/Basic/SourceManager.h"  // Story #23: For #line directives
#include <vector>  // For multi-dimensional array handling
#include <string>  // For std::to_string

using namespace clang;
using namespace llvm;

// Constructor: Initialize with output stream and context
// Story #22: Configure PrintingPolicy for C99 output
CodeGenerator::CodeGenerator(raw_ostream &OS, ASTContext &Ctx, const std::string &currentFile)
    : OS(OS), Policy(createC99Policy(Ctx)), Context(Ctx), CurrentInputFile(currentFile) {
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
    Policy.PolishForDeclaration = true;  // Include initializers in variable declarations

    // DRY: Reuse Clang's well-tested policy defaults for everything else
    return Policy;
}

// Print a declaration using Clang's DeclPrinter
// Dependency Inversion: Depends on Clang's abstract Decl interface
// Phase 35-02: Fixed to convert C++ references to C pointers in all function declarations
// Bug #35 FIX: Skip VarDecl in headers (local variables belong in function bodies)
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
    } else if (auto *ED = dyn_cast<EnumDecl>(D)) {
        // Bug #23: Print enum as typedef enum for C compatibility
        // BUG #2 FIX: Enums should only be in header files (like structs)
        // Enum definitions are type definitions, not function implementations
        // Phase 47 (Bug Fix): Enum deduplication is now handled in CppToCVisitor::VisitEnumDecl
        // by filtering which enums are added to C_TranslationUnit based on file basenames
        if (declarationOnly) {
            printEnumDecl(ED);
        }
        // When declarationOnly=false, skip enum definitions (already in header)
    } else if (auto *RD = dyn_cast<RecordDecl>(D)) {
        // Bug #24: Use custom printer for struct to add 'struct' prefixes
        // Struct definitions should only be in header files
        if (declarationOnly) {
            // Fixed: RecordHandler already ensures structs are in correct C_TU
            // No need to filter by source file location
            llvm::outs() << "[CodeGenerator] Emitting struct " << RD->getNameAsString() << " to header\n";
            printStructDecl(RD);
            OS << ";\n";
        }
        // When declarationOnly=false, skip struct definitions (already in header)
    } else if (auto *VD = dyn_cast<VarDecl>(D)) {
        // Bug #35 FIX: Skip ONLY local variables (they belong in function bodies)
        // Global variables MUST be emitted, including hoisted static locals
        // Check DeclContext instead of isLocalVarDecl() - hoisted statics are at TU level
        if (VD->isLocalVarDecl() && !isa<TranslationUnitDecl>(VD->getDeclContext())) {
            llvm::outs() << "[Bug #35] Skipping local VarDecl at top level: "
                         << VD->getNameAsString() << "\n";
            return;
        }
        // If it's at TU level, emit it even if isLocalVarDecl() returns true (hoisted static)
        if (isa<TranslationUnitDecl>(VD->getDeclContext())) {
            llvm::outs() << "[CodeGenerator] Emitting global/hoisted VarDecl: "
                         << VD->getNameAsString() << "\n";
        }

        // Emit global variable
        if (declarationOnly) {
            // Header file: emit extern declaration (only if not static)
            if (VD->getStorageClass() != SC_Static) {
                OS << "extern ";
                printCType(VD->getType());
                OS << " " << VD->getNameAsString() << ";\n";
            }
        } else {
            // Implementation file: emit full definition with initializer
            // CRITICAL FIX: For array types, we can't use printCType() + name
            // because C syntax requires: int arr[5], not int[5] arr
            // Use Clang's built-in printer which handles this correctly
            VD->print(OS, Policy);
            OS << ";\n";
        }
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

    // Bug #21 fix: Handle CompoundStmt recursively to intercept DeclStmt
    // We need to recursively handle statements to check for RecoveryExpr in DeclStmt
    if (CompoundStmt *CS = dyn_cast<CompoundStmt>(S)) {
        OS << std::string(Indent, '\t') << "{\n";
        for (Stmt *Child : CS->body()) {
            printStmt(Child, Indent + 1);
        }
        OS << std::string(Indent, '\t') << "}\n";
        return;
    }

    // Bug #26 fix: Handle ReturnStmt manually to print translated AST
    // ReturnStmt nodes created by translateReturnStmt() need manual printing
    // because printPretty() looks at source locations and prints original source
    if (ReturnStmt *RS = dyn_cast<ReturnStmt>(S)) {
        OS << std::string(Indent, '\t') << "return";
        if (Expr *RetValue = RS->getRetValue()) {
            OS << " ";
            printExpr(RetValue);  // Use printExpr, not printStmt, to avoid extra semicolon
        }
        OS << ";\n";
        return;
    }

    // Bug #26 fix: Handle IfStmt manually to print translated branches
    if (IfStmt *IS = dyn_cast<IfStmt>(S)) {
        OS << std::string(Indent, '\t') << "if (";
        if (Expr *Cond = IS->getCond()) {
            printExpr(Cond);  // Bug #37,40,41: Use printExpr for C-compatible syntax
        }
        OS << ") ";
        if (Stmt *Then = IS->getThen()) {
            if (isa<CompoundStmt>(Then)) {
                printStmt(Then, Indent);  // Compound stmt handles its own braces
            } else {
                OS << "{\n";
                printStmt(Then, Indent + 1);
                OS << std::string(Indent, '\t') << "}";
            }
        }
        if (Stmt *Else = IS->getElse()) {
            OS << " else ";
            if (isa<CompoundStmt>(Else)) {
                printStmt(Else, Indent);
            } else if (isa<IfStmt>(Else)) {
                printStmt(Else, Indent);  // else if
            } else {
                OS << "{\n";
                printStmt(Else, Indent + 1);
                OS << std::string(Indent, '\t') << "}";
            }
        }
        OS << "\n";
        return;
    }

    // Bug #26 fix: Handle SwitchStmt manually to print translated cases
    if (SwitchStmt *SS = dyn_cast<SwitchStmt>(S)) {
        OS << std::string(Indent, '\t') << "switch (";
        if (Expr *Cond = SS->getCond()) {
            printExpr(Cond);  // Bug #37,40,41: Use printExpr for C-compatible syntax
        }
        OS << ") ";
        if (Stmt *Body = SS->getBody()) {
            printStmt(Body, Indent);
        }
        OS << "\n";
        return;
    }

    // Bug #26 fix: Handle CaseStmt manually
    // Bug #37 fix: Use printExpr instead of printPretty to handle enum constants
    if (CaseStmt *CS = dyn_cast<CaseStmt>(S)) {
        OS << std::string(Indent, '\t') << "case ";
        if (Expr *LHS = CS->getLHS()) {
            printExpr(LHS);  // Bug #37: Use printExpr to convert GameState::Menu -> Menu
        }
        OS << ":\n";
        if (Stmt *SubStmt = CS->getSubStmt()) {
            printStmt(SubStmt, Indent + 1);
        }
        return;
    }

    // Bug #26 fix: Handle DefaultStmt manually
    if (DefaultStmt *DS = dyn_cast<DefaultStmt>(S)) {
        OS << std::string(Indent, '\t') << "default:\n";
        if (Stmt *SubStmt = DS->getSubStmt()) {
            printStmt(SubStmt, Indent + 1);
        }
        return;
    }

    // Phase 47: Handle DeclStmt manually to use custom expression printing
    if (DeclStmt *DS = dyn_cast<DeclStmt>(S)) {
        OS << std::string(Indent, '\t');
        // Print each declaration in the DeclStmt
        bool first = true;
        for (auto *D : DS->decls()) {
            if (!first) OS << ", ";
            first = false;

            if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
                // BUG FIX: Handle array types correctly (int arr[5] not int[5] arr)
                // CRITICAL: Handle multi-dimensional arrays (int arr[2][3] not int[3] arr[2])
                QualType VarType = VD->getType();

                if (const ArrayType *AT = VarType->getAsArrayTypeUnsafe()) {
                    // For array types, print: element_type name[size1][size2]...
                    // Get the element type recursively and collect all dimensions
                    QualType ElementType = VarType;
                    std::vector<std::string> dimensions;

                    // Collect all dimensions from outermost to innermost
                    while (const ArrayType *CurrentAT = ElementType->getAsArrayTypeUnsafe()) {
                        if (const ConstantArrayType *CAT = dyn_cast<ConstantArrayType>(CurrentAT)) {
                            dimensions.push_back("[" + std::to_string(CAT->getSize().getZExtValue()) + "]");
                        } else {
                            // Incomplete array type: int arr[]
                            dimensions.push_back("[]");
                        }
                        ElementType = CurrentAT->getElementType();
                    }

                    // Print: element_type name[dim1][dim2]...
                    printCType(ElementType);
                    OS << " " << VD->getNameAsString();
                    // Print dimensions in order
                    for (const std::string& dim : dimensions) {
                        OS << dim;
                    }
                } else {
                    // Non-array type: print normally
                    printCType(VarType);
                    OS << " " << VD->getNameAsString();
                }

                // Print initializer if present
                if (VD->hasInit()) {
                    OS << " = ";
                    printExpr(VD->getInit());  // Use custom printExpr to handle enum constants
                }
            } else {
                // For other declaration types, use default printing
                D->print(OS, Policy);
            }
        }
        OS << ";\n";
        return;
    }

    // Bug #26 fix: Handle WhileStmt manually
    if (WhileStmt *WS = dyn_cast<WhileStmt>(S)) {
        OS << std::string(Indent, '\t') << "while (";
        if (Expr *Cond = WS->getCond()) {
            printExpr(Cond);  // Bug #37,40,41: Use printExpr for C-compatible syntax
        }
        OS << ") ";
        if (Stmt *Body = WS->getBody()) {
            if (isa<CompoundStmt>(Body)) {
                printStmt(Body, Indent);
            } else {
                OS << "{\n";
                printStmt(Body, Indent + 1);
                OS << std::string(Indent, '\t') << "}\n";
            }
        } else {
            OS << "{}\n";
        }
        return;
    }

    // Bug #21 fix: Handle DeclStmt with RecoveryExpr specially
    // RecoveryExpr causes literal "<recovery-expr>()" to appear in generated C code
    // Solution: Print variable declarations without initializers if they contain RecoveryExpr
    if (DeclStmt *DS = dyn_cast<DeclStmt>(S)) {
        bool hasRecoveryExpr = false;

        // Check all declarations in this DeclStmt for RecoveryExpr
        for (Decl *D : DS->decls()) {
            if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
                if (Expr *Init = VD->getInit()) {
                    if (containsRecoveryExpr(Init)) {
                        hasRecoveryExpr = true;
                        break;
                    }
                }
            }
        }

        if (hasRecoveryExpr) {
            // Print declarations without initializers
            for (Decl *D : DS->decls()) {
                if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
                    OS << std::string(Indent, '\t');
                    VD->getType().print(OS, Policy);
                    OS << " " << VD->getNameAsString() << ";\n";
                }
            }
            return;
        }
    }

    // Handle ForStmt manually to avoid extra semicolons after closing brace
    if (ForStmt *FS = dyn_cast<ForStmt>(S)) {
        OS << std::string(Indent, '\t') << "for (";

        // Print initialization
        if (Stmt *Init = FS->getInit()) {
            if (DeclStmt *DS = dyn_cast<DeclStmt>(Init)) {
                // Print declaration without newline/indentation
                bool first = true;
                for (auto *D : DS->decls()) {
                    if (!first) OS << ", ";
                    first = false;
                    if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
                        printCType(VD->getType());
                        OS << " " << VD->getNameAsString();
                        if (VD->hasInit()) {
                            OS << " = ";
                            printExpr(VD->getInit());
                        }
                    }
                }
            } else {
                // Expression initialization
                printExpr(dyn_cast<Expr>(Init));
            }
        }
        OS << "; ";

        // Print condition
        if (Expr *Cond = FS->getCond()) {
            printExpr(Cond);
        }
        OS << "; ";

        // Print increment
        if (Expr *Inc = FS->getInc()) {
            printExpr(Inc);
        }
        OS << ") ";

        // Print body
        if (Stmt *Body = FS->getBody()) {
            if (isa<CompoundStmt>(Body)) {
                printStmt(Body, Indent);
            } else {
                OS << "{\n";
                printStmt(Body, Indent + 1);
                OS << std::string(Indent, '\t') << "}\n";
            }
        } else {
            OS << "{}\n";
        }
        return;
    }

    // Bug #42 fix: Handle BinaryOperator manually to use printExpr for C-compatible syntax
    // This ensures member calls, enum constants, etc. in binary expressions are translated
    // Example: sm.getCurrentState() -> StateMachine_getCurrentState(&sm)
    // Example: GameState::Menu -> GameState__Menu
    if (BinaryOperator *BO = dyn_cast<BinaryOperator>(S)) {
        OS << std::string(Indent, '\t');
        printExpr(BO->getLHS());
        OS << " " << BO->getOpcodeStr().str() << " ";
        printExpr(BO->getRHS());
        OS << ";\n";
        return;
    }

    // Handle CallExpr as statement to avoid "template" keyword artifacts
    // Constructor calls like: Base__ctor__void((struct Base *)this);
    // Using printExpr() instead of printPretty() avoids "template" keyword emission
    if (CallExpr *CE = dyn_cast<CallExpr>(S)) {
        OS << std::string(Indent, '\t');
        printExpr(CE);
        OS << ";\n";
        return;
    }

    // Use Clang's built-in StmtPrinter (via Stmt::printPretty)
    // KISS: Leverage existing, tested infrastructure
    OS << std::string(Indent, '\t');
    S->printPretty(OS, nullptr, Policy, 0);  // Use 0 indent since we handle it above

    // Bug #22: Add semicolon for bare expressions
    // When we recursively handle CompoundStmt, some child "statements" are actually
    // bare expressions (like BinaryOperator for assignments) created by AST builder.
    // These need semicolons, but printPretty() doesn't add them for expressions.
    // Note: Real statement types (ReturnStmt, DeclStmt, etc.) already have semicolons
    // from printPretty(), so we only add semicolons for Expr nodes.
    if (isa<Expr>(S)) {
        OS << ";";
    }
    OS << "\n";
}

// Bug #21: Helper to check if expression contains RecoveryExpr
bool CodeGenerator::containsRecoveryExpr(Expr *E) {
    if (!E) return false;

    // Check if this expression itself is a RecoveryExpr
    if (isa<RecoveryExpr>(E)) {
        return true;
    }

    // Recursively check all child expressions
    for (Stmt *Child : E->children()) {
        if (Expr *ChildExpr = dyn_cast_or_null<Expr>(Child)) {
            if (containsRecoveryExpr(ChildExpr)) {
                return true;
            }
        }
    }

    return false;
}

// Bug #23 / Phase 47 Task 2: Print enum as typedef enum for C compatibility
void CodeGenerator::printEnumDecl(EnumDecl *ED) {
    if (!ED) return;

    // Phase 47 Group 1 Task 2: Decision - use typedef or inline enum?
    // For C99 compatibility, always use typedef (see shouldUseTypedef())
    bool useTypedef = shouldUseTypedef(ED);

    if (useTypedef) {
        // C99 approach: typedef enum { ... } TypeName;
        OS << "typedef enum {\n";
    } else {
        // C23 approach (future): enum Name : Type { ... };
        // Not implemented yet - would emit: enum Name : type {\n
        OS << "enum " << ED->getNameAsString() << " {\n";
    }

    // Print enumerators
    bool first = true;
    for (EnumConstantDecl *ECD : ED->enumerators()) {
        if (!first) {
            OS << ",\n";
        }
        first = false;

        OS << "    " << ECD->getNameAsString();

        // Print initializer value if present
        const llvm::APSInt &Val = ECD->getInitVal();
        if (!ECD->getInitExpr() || Val != 0) {
            OS << " = " << Val;
        }
    }

    // Close enum declaration
    if (useTypedef) {
        // C99: closing brace with typedef name
        OS << "\n} " << ED->getNameAsString() << ";\n";
    } else {
        // C23 (future): just closing brace
        OS << "\n};\n";
    }
}

// Bug #24: Print struct with 'struct' prefix for field types
void CodeGenerator::printStructDecl(RecordDecl *RD) {
    if (!RD) return;

    // Print struct declaration
    OS << "struct " << RD->getNameAsString() << " {\n";

    // Print fields with proper 'struct' prefixes
    for (auto *Field : RD->fields()) {
        OS << "\t";

        QualType FieldType = Field->getType();

        // For array types, we need to print: element_type name[size]
        if (const ArrayType *AT = FieldType->getAsArrayTypeUnsafe()) {
            // Get element type (e.g., float for float[9])
            QualType ElementType = AT->getElementType();
            printCType(ElementType);
            OS << " " << Field->getNameAsString();

            // Manually construct array dimensions
            // For ConstantArrayType, print [size]
            if (const ConstantArrayType *CAT = dyn_cast<ConstantArrayType>(AT)) {
                OS << "[" << CAT->getSize().getZExtValue() << "]";
            } else {
                // For other array types (variable length, etc.), use Clang's printer
                // Print just the brackets part
                std::string TypeStr;
                llvm::raw_string_ostream TempOS(TypeStr);
                FieldType.print(TempOS, Policy);
                TempOS.flush();
                // Extract just the brackets (everything after the first '[')
                size_t BracketPos = TypeStr.find('[');
                if (BracketPos != std::string::npos) {
                    OS << TypeStr.substr(BracketPos);
                }
            }
        } else {
            // Non-array types: use our custom printer for 'struct' prefixes
            printCType(FieldType);
            OS << " " << Field->getNameAsString();
        }

        OS << ";\n";
    }

    OS << "}";
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
    // Structs need declarationOnly=true (they go in headers)
    bool isStruct = (D && llvm::isa<clang::RecordDecl>(D));
    printDecl(D, isStruct);
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
            // Structs and enums need declarationOnly=true to be printed
            // (they were originally designed to go in headers, but in E2E tests we put everything in one file)
            bool isStructOrEnum = llvm::isa<clang::RecordDecl>(D) || llvm::isa<clang::EnumDecl>(D);
            printDecl(D, isStructOrEnum);
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

        // CRITICAL FIX: Handle array types specially
        // In C, array parameters have special syntax: int arr[][3] not int (*)[3] arr
        // NOTE: Clang represents "int arr[][3]" as "int (*)[3]" (pointer to array)
        // We need to detect this and convert back to array syntax

        QualType ElementType = ParamType;
        std::vector<std::string> dimensions;
        bool isArrayParam = false;

        // Check if it's a pointer-to-array (canonical form of multi-dim array parameter)
        if (const PointerType *PT = ParamType->getAs<PointerType>()) {
            QualType PointeeType = PT->getPointeeType();
            if (const ArrayType *AT = PointeeType->getAsArrayTypeUnsafe()) {
                // This is pointer-to-array: int (*)[3]
                // Convert to: int [][3]
                isArrayParam = true;
                dimensions.push_back("[]");  // First dimension is always empty for params
                ElementType = PointeeType;

                // Collect remaining array dimensions
                while (const ArrayType *CurrentAT = ElementType->getAsArrayTypeUnsafe()) {
                    if (const ConstantArrayType *CAT = dyn_cast<ConstantArrayType>(CurrentAT)) {
                        dimensions.push_back("[" + std::to_string(CAT->getSize().getZExtValue()) + "]");
                    } else {
                        dimensions.push_back("[]");
                    }
                    ElementType = CurrentAT->getElementType();
                }
            }
        }
        // Also check for direct array types (less common for parameters)
        else if (const ArrayType *AT = ParamType->getAsArrayTypeUnsafe()) {
            isArrayParam = true;
            // Collect all dimensions
            while (const ArrayType *CurrentAT = ElementType->getAsArrayTypeUnsafe()) {
                if (const ConstantArrayType *CAT = dyn_cast<ConstantArrayType>(CurrentAT)) {
                    dimensions.push_back("[" + std::to_string(CAT->getSize().getZExtValue()) + "]");
                } else {
                    dimensions.push_back("[]");
                }
                ElementType = CurrentAT->getElementType();
            }
        }

        if (isArrayParam) {
            // Print: element_type name[dim1][dim2]...
            printCType(ElementType);
            if (!Param->getNameAsString().empty()) {
                OS << " " << Param->getNameAsString();
            }
            // Print dimensions in order
            for (const std::string& dim : dimensions) {
                OS << dim;
            }
        } else {
            // Non-array parameter: use normal printing
            printCType(ParamType);
            if (!Param->getNameAsString().empty()) {
                OS << " " << Param->getNameAsString();
            }
        }
    }
    OS << ")";
}

// Bug #37, #40, #41: Print expression with C-compatible syntax
// Handles:
// - DeclRefExpr to EnumConstantDecl: GameState::Menu -> Menu
// Pipeline Stage 3: Emit C AST to C source code
// IMPORTANT: This method should ONLY receive C AST nodes, not C++ nodes.
// All translation from C++ to C happens in Stage 2 (CppToCVisitor + handlers).
//
// Pipeline Separation:
// - Stage 2 creates C AST with correct names (e.g., "GameState__Menu", "Class_method")
// - Stage 3 simply emits what's in the C AST
//
// See INVESTIGATION_CODEGEN_PIPELINE_VIOLATIONS.md for details.
void CodeGenerator::printExpr(Expr *E) {
    if (!E) {
        OS << "/* null expr */";
        return;
    }

    // PIPELINE VIOLATION DETECTION:
    // C AST should NOT contain C++-specific nodes. If we see them, Stage 2 is broken.
    // These assertions enforce pipeline separation and catch bugs early.

    Expr *Unwrapped = E->IgnoreImpCasts();

    // Assert: C AST should not contain CXXMemberCallExpr
    // Stage 2 (CXXMemberCallExprHandler) should create CallExpr instead
    if (isa<CXXMemberCallExpr>(Unwrapped)) {
        llvm::errs() << "ERROR: C AST contains CXXMemberCallExpr - pipeline violation!\n";
        llvm::errs() << "Stage 2 (CXXMemberCallExprHandler) should create CallExpr.\n";
        llvm::errs() << "Expression: ";
        Unwrapped->dump();
        assert(false && "Pipeline violation: CXXMemberCallExpr in C AST");
    }

    // Assert: C AST should not contain CXXOperatorCallExpr
    // Stage 2 handlers should create CallExpr or BinaryOperator instead
    if (isa<CXXOperatorCallExpr>(Unwrapped)) {
        llvm::errs() << "ERROR: C AST contains CXXOperatorCallExpr - pipeline violation!\n";
        llvm::errs() << "Stage 2 should create CallExpr or BinaryOperator.\n";
        llvm::errs() << "Expression: ";
        Unwrapped->dump();
        assert(false && "Pipeline violation: CXXOperatorCallExpr in C AST");
    }

    // Assert: C AST should not contain CXXConstructExpr (unless wrapped in CompoundLiteralExpr)
    // Stage 2 (CXXConstructExprHandler) should create CompoundLiteralExpr
    if (isa<CXXConstructExpr>(Unwrapped) && !isa<CompoundLiteralExpr>(E)) {
        llvm::errs() << "ERROR: C AST contains unwrapped CXXConstructExpr - pipeline violation!\n";
        llvm::errs() << "Stage 2 (CXXConstructExprHandler) should wrap in CompoundLiteralExpr.\n";
        llvm::errs() << "Expression: ";
        Unwrapped->dump();
        assert(false && "Pipeline violation: unwrapped CXXConstructExpr in C AST");
    }

    // Assert: CallExpr in C AST should reference FunctionDecl, not CXXMethodDecl
    // Stage 2 should create regular FunctionDecl for translated methods
    if (CallExpr *CE = dyn_cast<CallExpr>(Unwrapped)) {
        if (!isa<CXXOperatorCallExpr>(CE) && !isa<CXXMemberCallExpr>(CE)) {
            if (Expr *Callee = CE->getCallee()) {
                if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(Callee->IgnoreImpCasts())) {
                    if (isa<CXXMethodDecl>(DRE->getDecl())) {
                        llvm::errs() << "ERROR: C AST CallExpr references CXXMethodDecl - pipeline violation!\n";
                        llvm::errs() << "Stage 2 should create FunctionDecl for translated methods.\n";
                        llvm::errs() << "Method: " << DRE->getDecl()->getNameAsString() << "\n";
                        assert(false && "Pipeline violation: CallExpr references CXXMethodDecl in C AST");
                    }
                }
            }
        }
    }

    // LEGITIMATE C NODE HANDLING:
    // The following are valid C nodes that need custom emission logic.

    // Handle BinaryOperator with recursive emission for subexpressions
    // This is a legitimate C node (e.g., a + b, a == b)
    if (BinaryOperator *BO = dyn_cast<BinaryOperator>(Unwrapped)) {
        printExpr(BO->getLHS());
        OS << " " << BO->getOpcodeStr().str() << " ";
        printExpr(BO->getRHS());
        return;
    }

    // Handle ParenExpr with recursive emission
    // This is a legitimate C node (e.g., (a + b))
    if (ParenExpr *PE = dyn_cast<ParenExpr>(E)) {
        OS << "(";
        printExpr(PE->getSubExpr());
        OS << ")";
        return;
    }

    // Handle CompoundLiteralExpr to ensure "struct" keyword is emitted
    // This is a legitimate C99 node (e.g., (struct Point){1, 2})
    // CXXConstructExprHandler creates CompoundLiteralExpr for C99 struct literals
    // but Clang's printPretty doesn't always include "struct" keyword
    if (CompoundLiteralExpr *CLE = dyn_cast<CompoundLiteralExpr>(E)) {
        QualType Type = CLE->getType();
        if (const RecordType *RT = Type->getAs<RecordType>()) {
            // This is a struct type, emit "(struct TypeName){...}"
            OS << "(struct " << RT->getDecl()->getNameAsString() << ")";
            if (Expr *Init = CLE->getInitializer()) {
                printExpr(Init);
            }
            return;
        }
    }

    // Handle CStyleCastExpr to avoid "template" keyword artifacts
    // Clang's printPretty() can emit "template" before type names in certain contexts
    // For C code, we just want: (TypeName)expr
    if (CStyleCastExpr *CSE = dyn_cast<CStyleCastExpr>(E)) {
        QualType Type = CSE->getType();
        OS << "(";
        Type.print(OS, Policy);
        OS << ")";
        printExpr(CSE->getSubExpr());
        return;
    }

    // Handle UnaryOperator to avoid "template" keyword artifacts
    // Handles operators like &, *, -, !, etc.
    if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
        OS << UnaryOperator::getOpcodeStr(UO->getOpcode()).str();
        printExpr(UO->getSubExpr());
        return;
    }

    // Handle DeclRefExpr to avoid "template" keyword artifacts
    // Clang's printPretty() can emit "template" before variable/function names
    // For C code, we just want the simple name
    if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(E)) {
        if (ValueDecl *VD = DRE->getDecl()) {
            OS << VD->getNameAsString();
        }
        return;
    }

    // Handle MemberExpr to avoid "template" keyword artifacts
    // Clang's printPretty() can emit "template" before member accesses
    // For C code, we want: base.member or base->member
    if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
        printExpr(ME->getBase());
        OS << (ME->isArrow() ? "->" : ".");
        OS << ME->getMemberDecl()->getNameAsString();
        return;
    }

    // Handle CallExpr to avoid "template" keyword artifacts
    // Clang's printPretty() can emit "template" before function names and arguments
    // For C code, we just want: function(arg1, arg2, ...)
    if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
        // Print callee (function name or expression)
        printExpr(CE->getCallee());
        OS << "(";
        // Print arguments
        for (unsigned i = 0, e = CE->getNumArgs(); i != e; ++i) {
            if (i > 0) OS << ", ";
            printExpr(CE->getArg(i));
        }
        OS << ")";
        return;
    }

    // DEFAULT: Use printPretty for all other C nodes
    // C AST nodes (DeclRefExpr, CallExpr, IntegerLiteral, etc.) already have correct names
    // - EnumConstantDecl has prefixed name (e.g., "GameState__Menu")
    // - FunctionDecl has translated name (e.g., "Class_method")
    // - DeclRefExpr points to C declarations with correct names
    //
    // No translation logic needed - just emit what's in the C AST.
    E->printPretty(OS, nullptr, Policy, 0);
}
