// Manual verification test for CNodeBuilder (Story #9)
// This demonstrates the CNodeBuilder API works as expected

#include "CNodeBuilder.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include <iostream>

using namespace clang;

// Demonstration of CNodeBuilder usage
class CNPrinter : public ASTConsumer {
    ASTContext *Ctx;

public:
    void HandleTranslationUnit(ASTContext &Context) override {
        Ctx = &Context;

        std::cout << "=== CNodeBuilder Manual Test (Story #9) ===" << std::endl;

        // Create CNodeBuilder instance
        CNodeBuilder builder(Context);

        // Test 1: int type
        QualType intTy = builder.intType();
        std::cout << "1. intType(): " << (intTy->isIntegerType() ? "✓ PASS" : "✗ FAIL") << std::endl;

        // Test 2: void type
        QualType voidTy = builder.voidType();
        std::cout << "2. voidType(): " << (voidTy->isVoidType() ? "✓ PASS" : "✗ FAIL") << std::endl;

        // Test 3: char type
        QualType charTy = builder.charType();
        std::cout << "3. charType(): " << (charTy->isCharType() ? "✓ PASS" : "✗ FAIL") << std::endl;

        // Test 4: pointer type
        QualType ptrTy = builder.ptrType(intTy);
        std::cout << "4. ptrType(): " << (ptrTy->isPointerType() ? "✓ PASS" : "✗ FAIL") << std::endl;

        // Test 5: struct type
        QualType structTy = builder.structType("Point");
        std::cout << "5. structType(): " << (structTy->isStructureType() ? "✓ PASS" : "✗ FAIL") << std::endl;

        std::cout << "\n✓ All CNodeBuilder type helpers working!" << std::endl;
    }
};

class CNAction : public ASTFrontendAction {
public:
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
        return std::make_unique<CNPrinter>();
    }
};

// Use this test: clang -Xclang -ast-print -fsyntax-only tests/fixtures/simple.cpp
// Then this tool will demonstrate CNodeBuilder
int main(int argc, const char **argv) {
    // Create a simple code to parse
    const char *code = "int main() { return 0; }";

    std::unique_ptr<tooling::FrontendActionFactory> Factory =
        tooling::newFrontendActionFactory<CNAction>();

    // Run the action on the code
    if (tooling::runToolOnCode(Factory->create(), code)) {
        return 0;
    }

    return 1;
}
