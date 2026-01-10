/**
 * Unit test for DeclContext parent-child relationship
 * Tests that FunctionDecl appears in TranslationUnitDecl::decls() after addDecl()
 */

#include <gtest/gtest.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/DeclBase.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <memory>
#include <string>

using namespace clang;

class DeclContextTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        std::vector<std::string> args = {"-std=c++17", "-xc++"};
        return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    }
};

// Test 1: Verify that FunctionDecl created with TranslationUnitDecl appears in decls()
TEST_F(DeclContextTest, FunctionDeclAppearsInDecls) {
    const char *code = "void existingFunc() {}";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    ASTContext &Ctx = AST->getASTContext();
    TranslationUnitDecl *TU = Ctx.getTranslationUnitDecl();

    // Print initial state
    llvm::outs() << "\n=== Test 1: Initial TU state ===\n";
    llvm::outs() << "TU pointer:         " << (void*)TU << "\n";
    llvm::outs() << "TU as DeclContext*: " << (void*)static_cast<DeclContext*>(TU) << "\n";
    llvm::outs() << "Offset:             " << ((char*)static_cast<DeclContext*>(TU) - (char*)TU) << " bytes\n";

    int initialCount = 0;
    for (Decl *D : TU->decls()) {
        initialCount++;
        if (FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
            llvm::outs() << "  Found existing: " << FD->getNameAsString() << "\n";
        }
    }
    llvm::outs() << "Initial decl count: " << initialCount << "\n\n";

    // Create a new FunctionDecl
    llvm::outs() << "=== Creating new FunctionDecl ===\n";
    IdentifierInfo &FuncII = Ctx.Idents.get("newTestFunc");
    DeclarationName FuncName(&FuncII);

    QualType IntTy = Ctx.IntTy;
    FunctionProtoType::ExtProtoInfo EPI;
    QualType FuncType = Ctx.getFunctionType(IntTy, {}, EPI);

    // Create with TU as DeclContext
    FunctionDecl *NewFunc = FunctionDecl::Create(
        Ctx,
        TU,  // Use the same TU we're iterating
        SourceLocation(),
        SourceLocation(),
        FuncName,
        FuncType,
        Ctx.getTrivialTypeSourceInfo(FuncType),
        SC_None
    );

    llvm::outs() << "NewFunc pointer:           " << (void*)NewFunc << "\n";
    llvm::outs() << "NewFunc->getDeclContext(): " << (void*)NewFunc->getDeclContext() << "\n";
    llvm::outs() << "TU as DeclContext*:        " << (void*)static_cast<DeclContext*>(TU) << "\n";
    llvm::outs() << "Pointers match? " << (NewFunc->getDeclContext() == static_cast<DeclContext*>(TU) ? "YES" : "NO") << "\n\n";

    // Add to TU
    llvm::outs() << "=== Calling TU->addDecl(NewFunc) ===\n";
    TU->addDecl(NewFunc);

    // Iterate and check
    int afterCount = 0;
    bool foundNew = false;
    for (Decl *D : TU->decls()) {
        afterCount++;
        if (FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
            llvm::outs() << "  [" << afterCount << "] " << FD->getNameAsString();
            if (FD == NewFunc) {
                llvm::outs() << " <- OUR NEW FUNCTION";
                foundNew = true;
            }
            llvm::outs() << "\n";
        }
    }
    llvm::outs() << "After addDecl count: " << afterCount << "\n";
    llvm::outs() << "NewFunc found in iteration? " << (foundNew ? "YES" : "NO") << "\n\n";

    ASSERT_TRUE(foundNew) << "New function should appear in TU->decls() after addDecl()";
}

// Test 2: Test creating FunctionDecl with one TU and adding to a different TU
// LLVM 21 BEHAVIOR: This now SUCCEEDS (different from older LLVM versions)
// Documents that addDecl() does NOT validate parent-child consistency
// WARNING: This means transpiler must be careful to create Decls with correct parent!
TEST_F(DeclContextTest, CrossTUAddDecl) {
    const char *code = "void existingFunc() {}";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    ASTContext &Ctx = AST->getASTContext();
    TranslationUnitDecl *GlobalTU = Ctx.getTranslationUnitDecl();

    // Create a second TU (simulating per-file TU)
    llvm::outs() << "\n=== Test 2: Cross-TU addDecl ===\n";
    TranslationUnitDecl *PerFileTU = TranslationUnitDecl::Create(Ctx);
    llvm::outs() << "GlobalTU pointer:     " << (void*)GlobalTU << "\n";
    llvm::outs() << "PerFileTU pointer:    " << (void*)PerFileTU << "\n\n";

    // Create FunctionDecl with GlobalTU
    IdentifierInfo &FuncII = Ctx.Idents.get("crossTUFunc");
    DeclarationName FuncName(&FuncII);

    QualType IntTy = Ctx.IntTy;
    FunctionProtoType::ExtProtoInfo EPI;
    QualType FuncType = Ctx.getFunctionType(IntTy, {}, EPI);

    llvm::outs() << "Creating FunctionDecl with GlobalTU as DeclContext:\n";
    FunctionDecl *CrossFunc = FunctionDecl::Create(
        Ctx,
        GlobalTU,  // Created with GlobalTU
        SourceLocation(),
        SourceLocation(),
        FuncName,
        FuncType,
        Ctx.getTrivialTypeSourceInfo(FuncType),
        SC_None
    );

    llvm::outs() << "CrossFunc->getDeclContext(): " << (void*)CrossFunc->getDeclContext() << "\n";
    llvm::outs() << "GlobalTU as DeclContext*:    " << (void*)static_cast<DeclContext*>(GlobalTU) << "\n";
    llvm::outs() << "PerFileTU as DeclContext*:   " << (void*)static_cast<DeclContext*>(PerFileTU) << "\n\n";

    // Try to add to PerFileTU - different parent
    // LLVM 21: This SUCCEEDS and Decl appears in iteration!
    // Older LLVM: Would assert in debug builds
    llvm::outs() << "Calling PerFileTU->addDecl(CrossFunc) - adding to different parent\n";
    PerFileTU->addDecl(CrossFunc);

    // Check if it appears
    int count = 0;
    bool found = false;
    for (Decl *D : PerFileTU->decls()) {
        count++;
        if (D == CrossFunc) {
            found = true;
        }
    }
    llvm::outs() << "PerFileTU->decls() count: " << count << "\n";
    llvm::outs() << "CrossFunc found? " << (found ? "YES" : "NO") << "\n";
    llvm::outs() << "CrossFunc->getDeclContext() still points to: " << (void*)CrossFunc->getDeclContext() << "\n";
    llvm::outs() << "GlobalTU? " << (CrossFunc->getDeclContext() == static_cast<DeclContext*>(GlobalTU) ? "YES" : "NO") << "\n";
    llvm::outs() << "PerFileTU? " << (CrossFunc->getDeclContext() == static_cast<DeclContext*>(PerFileTU) ? "YES" : "NO") << "\n\n";

    // LLVM 21: Decl appears in PerFileTU iteration but getDeclContext() still returns GlobalTU
    // This is INCONSISTENT state - Decl is in two parent-child relationships!
    // LESSON: Transpiler must create Decls with correct parent from the start
    ASSERT_TRUE(found) << "LLVM 21: Decl appears in iteration even with different parent";
    ASSERT_EQ(CrossFunc->getDeclContext(), static_cast<DeclContext*>(GlobalTU))
        << "LLVM 21: getDeclContext() still returns original parent (inconsistent!)";
}

// Test 3: Correct way - create with PerFileTU, add to PerFileTU
TEST_F(DeclContextTest, CorrectPerFileTUUsage) {
    const char *code = "void existingFunc() {}";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    ASTContext &Ctx = AST->getASTContext();
    TranslationUnitDecl *PerFileTU = TranslationUnitDecl::Create(Ctx);

    llvm::outs() << "\n=== Test 3: Correct PerFileTU usage ===\n";
    llvm::outs() << "PerFileTU pointer:    " << (void*)PerFileTU << "\n";
    llvm::outs() << "PerFileTU as DC*:     " << (void*)static_cast<DeclContext*>(PerFileTU) << "\n\n";

    // Create FunctionDecl with PerFileTU
    IdentifierInfo &FuncII = Ctx.Idents.get("correctFunc");
    DeclarationName FuncName(&FuncII);

    QualType IntTy = Ctx.IntTy;
    FunctionProtoType::ExtProtoInfo EPI;
    QualType FuncType = Ctx.getFunctionType(IntTy, {}, EPI);

    llvm::outs() << "Creating FunctionDecl with PerFileTU as DeclContext:\n";
    FunctionDecl *CorrectFunc = FunctionDecl::Create(
        Ctx,
        PerFileTU,  // Same TU we'll add to
        SourceLocation(),
        SourceLocation(),
        FuncName,
        FuncType,
        Ctx.getTrivialTypeSourceInfo(FuncType),
        SC_None
    );

    llvm::outs() << "CorrectFunc->getDeclContext(): " << (void*)CorrectFunc->getDeclContext() << "\n";
    llvm::outs() << "PerFileTU as DeclContext*:     " << (void*)static_cast<DeclContext*>(PerFileTU) << "\n";
    llvm::outs() << "Pointers match? " << (CorrectFunc->getDeclContext() == static_cast<DeclContext*>(PerFileTU) ? "YES" : "NO") << "\n\n";

    // Add to PerFileTU
    llvm::outs() << "Calling PerFileTU->addDecl(CorrectFunc):\n";
    PerFileTU->addDecl(CorrectFunc);

    // Check if it appears
    int count = 0;
    bool found = false;
    for (Decl *D : PerFileTU->decls()) {
        count++;
        if (FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
            llvm::outs() << "  [" << count << "] " << FD->getNameAsString();
            if (FD == CorrectFunc) {
                llvm::outs() << " <- OUR FUNCTION";
                found = true;
            }
            llvm::outs() << "\n";
        }
    }
    llvm::outs() << "Total: " << count << "\n";
    llvm::outs() << "CorrectFunc found? " << (found ? "YES (correct!)" : "NO (wrong!)") << "\n\n";

    ASSERT_TRUE(found) << "Function should appear when created and added to same TU";
}
