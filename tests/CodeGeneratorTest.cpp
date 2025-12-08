// Story #21: DeclPrinter/StmtPrinter Integration - Unit Tests
// Following TDD RED-GREEN-REFACTOR cycle

#include "CodeGenerator.h"
#include "CNodeBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <cassert>
#include <iostream>
#include <fstream>

using namespace clang;
using namespace llvm;

// Helper: Create a test ASTContext
std::unique_ptr<ASTUnit> createTestASTUnit() {
    std::vector<std::string> Args = {"-std=c99"};
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCodeWithArgs(
        "void dummy() {}", Args, "test.c"
    );
    assert(AST && "Failed to create test ASTUnit");
    return AST;
}

// Test 1: Print simple struct declaration
void testPrintStructDecl() {
    std::cout << "TEST: PrintStructDecl - ";

    auto AST = createTestASTUnit();
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
    bool hasStruct = Output.find("struct") != std::string::npos;
    bool hasPoint = Output.find("Point") != std::string::npos;
    bool hasX = Output.find("x") != std::string::npos;
    bool hasY = Output.find("y") != std::string::npos;

    if (hasStruct && hasPoint && hasX && hasY) {
        std::cout << "PASS" << std::endl;
    } else {
        std::cout << "FAIL" << std::endl;
        std::cout << "Output: " << Output << std::endl;
        exit(1);
    }
}

// Test 2: Print function declaration
void testPrintFunctionDecl() {
    std::cout << "TEST: PrintFunctionDecl - ";

    auto AST = createTestASTUnit();
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
    bool hasInt = Output.find("int") != std::string::npos;
    bool hasName = Output.find("Point_getX") != std::string::npos;
    bool hasThis = Output.find("this") != std::string::npos;

    if (hasInt && hasName && hasThis) {
        std::cout << "PASS" << std::endl;
    } else {
        std::cout << "FAIL" << std::endl;
        std::cout << "Output: " << Output << std::endl;
        exit(1);
    }
}

// Test 3: Print multiple declarations (TranslationUnit)
void testPrintTranslationUnit() {
    std::cout << "TEST: PrintTranslationUnit - ";

    auto AST = createTestASTUnit();
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
    bool hasStruct = Output.find("struct Point") != std::string::npos;
    bool hasFunc = Output.find("test_func") != std::string::npos;

    if (hasStruct && hasFunc) {
        std::cout << "PASS" << std::endl;
    } else {
        std::cout << "FAIL" << std::endl;
        std::cout << "Output: " << Output << std::endl;
        exit(1);
    }
}

// Test 4: Output to file
void testOutputToFile() {
    std::cout << "TEST: OutputToFile - ";

    auto AST = createTestASTUnit();
    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);

    // Create simple struct
    RecordDecl *RD = Builder.structDecl("TestStruct", {
        Builder.fieldDecl(Context.IntTy, "value")
    });

    // Generate to file
    std::error_code EC;
    raw_fd_ostream OutFile("/tmp/test_codegen_output.c", EC);

    if (EC) {
        std::cout << "FAIL - Could not create file: " << EC.message() << std::endl;
        exit(1);
    }

    CodeGenerator Gen(OutFile, Context);
    Gen.printDecl(RD);
    OutFile.flush();
    OutFile.close();

    // Read file back and verify
    std::ifstream InFile("/tmp/test_codegen_output.c");
    std::string Content((std::istreambuf_iterator<char>(InFile)),
                        std::istreambuf_iterator<char>());

    bool hasContent = Content.find("TestStruct") != std::string::npos;

    if (hasContent) {
        std::cout << "PASS" << std::endl;
    } else {
        std::cout << "FAIL" << std::endl;
        std::cout << "File content: " << Content << std::endl;
        exit(1);
    }
}

int main() {
    std::cout << "=== Story #21: CodeGenerator Tests ===" << std::endl;

    // TDD: These tests define the behavior we want
    testPrintStructDecl();
    testPrintFunctionDecl();
    testPrintTranslationUnit();
    testOutputToFile();

    std::cout << "\n✓ All tests PASSED - Story #21 complete!" << std::endl;
    return 0;
}
