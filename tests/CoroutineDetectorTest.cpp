// tests/CoroutineDetectorTest.cpp
// Unit tests for Coroutine Detection and Frame Structure (Story #102)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/CoroutineDetector.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {
        "-std=c++20",
        "-isystem", "/opt/homebrew/Cellar/llvm/21.1.7/include/c++/v1",
        "-isystem", "/opt/homebrew/Cellar/llvm/21.1.7/lib/clang/21/include",
        "-isysroot", "/Library/Developer/CommandLineTools/SDKs/MacOSX15.sdk"
    };
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        std::cerr << "  Condition: " #cond << std::endl; \
        return; \
    }

FunctionDecl* findFunction(TranslationUnitDecl* TU, const std::string& name) {
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == name) {
                return FD;
            }
        }
    }
    return nullptr;
}

// Test 1: Detect coroutine by co_return

// Test fixture
class CoroutineDetectorTest : public ::testing::Test {
protected:
};

TEST_F(CoroutineDetectorTest, NonCoroutineDetection) {
    const char *code = R"(
            int regular_function() {
                return 42;
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        CoroutineDetector detector(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "regular_function");

        ASSERT_TRUE(func) << "Function not found";
        ASSERT_TRUE(!detector.isCoroutine(func)) << "Should NOT detect regular function as coroutine";
}
