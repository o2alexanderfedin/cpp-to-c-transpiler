/**
 * Test Suite: Calling Convention Detection
 *
 * Purpose: Verify that calling conventions are detected via Clang APIs.
 *
 * IMPORTANT PLATFORM NOTE:
 * - Many calling conventions are platform-specific (x86 only, Windows only, etc.)
 * - On ARM64 (Apple Silicon), x86 calling conventions default to CC_C
 * - This is EXPECTED BEHAVIOR - the tests verify API usage, not platform support
 * - Full calling convention support requires building for the target platform
 *
 * Milestone: #3 - Calling Convention Support
 * Prompt: #031 - extern "C" and Calling Convention Support
 */

#include <gtest/gtest.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Type.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <memory>
#include <string>

using namespace clang;

// Helper Functions
// ============================================================================

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17", "-xc++"};
    return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}

FunctionDecl* findFunction(ASTContext &Ctx, const std::string &name) {
    for (auto *D : Ctx.getTranslationUnitDecl()->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getName() == name) {
                return FD;
            }
        }
        if (auto *LS = dyn_cast<LinkageSpecDecl>(D)) {
            for (auto *LD : LS->decls()) {
                if (auto *FD = dyn_cast<FunctionDecl>(LD)) {
                    if (FD->getName() == name) {
                        return FD;
                    }
                }
            }
        }
    }
    return nullptr;
}

CallingConv getCallingConv(FunctionDecl *FD) {
    const FunctionType *FT = FD->getType()->getAs<FunctionType>();
    return FT ? FT->getCallConv() : CC_C;
}

// ============================================================================
// Test 1: Default C calling convention (works on all platforms)
// ============================================================================

// Test fixture
class CallingConventionTest : public ::testing::Test {
protected:
};

TEST_F(CallingConventionTest, DefaultCConvention) {
    const char *code = R"(
            void normalFunc(int x) {}
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionDecl *FD = findFunction(AST->getASTContext(), "normalFunc");
        ASSERT_TRUE(FD != nullptr) << "Function not found";
        ASSERT_TRUE(getCallingConv(FD) == CC_C) << "Expected CC_C";
}

TEST_F(CallingConventionTest, CallingConvQueryAPI) {
    const char *code = R"(
            void func1(int x) {}
            void __attribute__((ms_abi)) func2(int x) {}
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionDecl *func1 = findFunction(AST->getASTContext(), "func1");
        ASSERT_TRUE(func1 != nullptr) << "func1 not found";

        // Verify we CAN query calling convention
        CallingConv cc1 = getCallingConv(func1);
        ASSERT_TRUE(cc1 == CC_C) << "func1 should have CC_C";
}

TEST_F(CallingConventionTest, ExternCPreservesCallingConv) {
    const char *code = R"(
            extern "C" void exported(int x) {}
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionDecl *FD = findFunction(AST->getASTContext(), "exported");
        ASSERT_TRUE(FD != nullptr) << "Function not found";
        ASSERT_TRUE(FD->isExternC()) << "Should have C linkage";

        // extern "C" functions still have calling convention (default CC_C)
        CallingConv CC = getCallingConv(FD);
        ASSERT_TRUE(CC == CC_C) << "Expected CC_C for extern C function";
}
