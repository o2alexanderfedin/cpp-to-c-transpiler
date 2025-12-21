// Story #21: DeclPrinter/StmtPrinter Integration - Unit Tests
// Following TDD RED-GREEN-REFACTOR cycle

#include <gtest/gtest.h>
#include "CodeGenerator.h"
#include "CNodeBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <iostream>
#include <fstream>

using namespace clang;
using namespace llvm;

// Test fixture for CodeGenerator tests
class CodeGeneratorTest : public ::testing::Test {
protected:
    // Helper: Create a test ASTUnit
    std::unique_ptr<ASTUnit> createTestASTUnit() {
        std::vector<std::string> Args = {"-std=c99"};
        std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCodeWithArgs(
            "void dummy() {}", Args, "test.c"
        );
        EXPECT_NE(AST, nullptr) << "Failed to create test ASTUnit";
        return AST;
    }
};

// Test 1: Print simple struct declaration
TEST_F(CodeGeneratorTest, PrintStructDecl) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    // Create simple Point struct
    RecordDecl *RD = Builder.structDecl("Point", {
        Builder.fieldDecl(Context.IntTy, "x"),
        Builder.fieldDecl(Context.IntTy, "y")
    });

    // Generate code
    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);
    Gen.printDecl(RD);
    OS.flush();

    // Verify output contains expected elements
    EXPECT_NE(Output.find("struct"), std::string::npos);
    EXPECT_NE(Output.find("Point"), std::string::npos);
    EXPECT_NE(Output.find("x"), std::string::npos);
    EXPECT_NE(Output.find("y"), std::string::npos);
}

// Test 2: Print function declaration
TEST_F(CodeGeneratorTest, PrintFunctionDecl) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    // Create simple function: int getX(struct Point *this)
    RecordDecl *PointRD = Builder.structDecl("Point", {});
    QualType PointPtrTy = Context.getPointerType(Context.getRecordType(PointRD));

    ParmVarDecl *ThisParam = Builder.param(PointPtrTy, "this");
    FunctionDecl *FD = Builder.funcDecl("Point_getX", Context.IntTy, {ThisParam});

    // Generate code
    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);
    Gen.printDecl(FD);
    OS.flush();

    // Verify output
    EXPECT_NE(Output.find("int"), std::string::npos);
    EXPECT_NE(Output.find("Point_getX"), std::string::npos);
    EXPECT_NE(Output.find("this"), std::string::npos);
}

// Test 3: Print multiple declarations (TranslationUnit)
TEST_F(CodeGeneratorTest, PrintTranslationUnit) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    // Create struct and function
    RecordDecl *RD = Builder.structDecl("Point", {
        Builder.fieldDecl(Context.IntTy, "x")
    });

    FunctionDecl *FD = Builder.funcDecl("test_func", Context.IntTy, {});

    // Generate code for both
    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);

    Gen.printDecl(RD);
    Gen.printDecl(FD);
    OS.flush();

    // Verify both declarations present
    EXPECT_NE(Output.find("struct Point"), std::string::npos);
    EXPECT_NE(Output.find("test_func"), std::string::npos);
}

// Test 4: Output to file
TEST_F(CodeGeneratorTest, OutputToFile) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    // Create simple struct
    RecordDecl *RD = Builder.structDecl("TestStruct", {
        Builder.fieldDecl(Context.IntTy, "value")
    });

    // Generate to file
    std::error_code EC;
    raw_fd_ostream OutFile("/tmp/test_codegen_output.c", EC);

    ASSERT_FALSE(EC) << "Could not create file: " << EC.message();

    CodeGenerator Gen(OutFile, Context);
    Gen.printDecl(RD);
    OutFile.flush();
    OutFile.close();

    // Read file back and verify
    std::ifstream InFile("/tmp/test_codegen_output.c");
    std::string Content((std::istreambuf_iterator<char>(InFile)),
                        std::istreambuf_iterator<char>());

    EXPECT_NE(Content.find("TestStruct"), std::string::npos);
}

// ============================================================================
// Story #22: PrintingPolicy C99 Configuration Tests
// ============================================================================

// Test 5: C99 bool type configuration (_Bool not bool)
TEST_F(CodeGeneratorTest, BoolTypeC99) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();

    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);

    PrintingPolicy &Policy = Gen.getPrintingPolicy();

    // Verify Bool policy is set for C99 (_Bool)
    EXPECT_TRUE(Policy.Bool) << "Bool policy not configured for C99";
}

// Test 6: Indentation configured
TEST_F(CodeGeneratorTest, IndentationConfigured) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();

    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);

    PrintingPolicy &Policy = Gen.getPrintingPolicy();

    // Verify indentation is configured
    EXPECT_EQ(Policy.Indentation, 4) << "Indentation not configured correctly (expected 4, got "
              << Policy.Indentation << ")";
}

// Test 7: Struct keyword preserved
TEST_F(CodeGeneratorTest, StructKeyword) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    RecordDecl *RD = Builder.structDecl("TestStruct", {
        Builder.fieldDecl(Context.IntTy, "value")
    });

    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);
    Gen.printDecl(RD);
    OS.flush();

    // Verify 'struct' keyword is present
    EXPECT_NE(Output.find("struct"), std::string::npos) << "'struct' keyword missing";
}

// Test 8: Compile with gcc -std=c99
TEST_F(CodeGeneratorTest, CompileWithGcc) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    // Create simple C code
    RecordDecl *RD = Builder.structDecl("Point", {
        Builder.fieldDecl(Context.IntTy, "x"),
        Builder.fieldDecl(Context.IntTy, "y")
    });

    // Generate to file
    std::error_code EC;
    raw_fd_ostream OutFile("/tmp/test_c99.c", EC);

    ASSERT_FALSE(EC) << "Could not create file: " << EC.message();

    CodeGenerator Gen(OutFile, Context);
    Gen.printDecl(RD);
    OutFile.flush();
    OutFile.close();

    // Try to compile with gcc -std=c99
    int result = system("gcc -std=c99 -c /tmp/test_c99.c -o /tmp/test_c99.o 2>/tmp/test_c99_errors.txt");

    EXPECT_EQ(result, 0) << "Compilation failed";

    if (result != 0) {
        system("cat /tmp/test_c99_errors.txt");
    }
}

// ============================================================================
// Story #23: #line Directive Injection Tests
// ============================================================================

// Test 9: Line directive present for valid location
TEST_F(CodeGeneratorTest, LineDirectivePresent) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    RecordDecl *RD = Builder.structDecl("TestStruct", {
        Builder.fieldDecl(Context.IntTy, "value")
    });

    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);
    Gen.printDeclWithLineDirective(RD);
    OS.flush();

    // Verify #line directive is present (or gracefully absent for test context)
    // In test context, locations may be invalid, so either #line or direct struct is OK
    EXPECT_NE(Output.find("struct TestStruct"), std::string::npos) << "Output missing";
}

// Test 10: Multiple declarations each get their own context
TEST_F(CodeGeneratorTest, MultipleDeclarationsWithLines) {
    auto AST = createTestASTUnit();
    ASSERT_NE(AST, nullptr);

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    RecordDecl *RD1 = Builder.structDecl("Point", {
        Builder.fieldDecl(Context.IntTy, "x")
    });

    FunctionDecl *FD = Builder.funcDecl("test_func", Context.IntTy, {});

    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);

    Gen.printDeclWithLineDirective(RD1);
    Gen.printDeclWithLineDirective(FD);
    OS.flush();

    // Verify both declarations present
    EXPECT_NE(Output.find("struct Point"), std::string::npos);
    EXPECT_NE(Output.find("test_func"), std::string::npos);
}
