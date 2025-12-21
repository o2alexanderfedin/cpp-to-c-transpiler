// tests/CallingConventionTest_GTest.cpp
// Migrated from CallingConventionTest.cpp to Google Test framework
// Milestone #3: Calling Convention Support
// Prompt #031: extern "C" and Calling Convention Support

#include <gtest/gtest.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Type.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <memory>
#include <string>

using namespace clang;

// Test fixture for Calling Convention tests
class CallingConventionTestFixture : public ::testing::Test {
protected:
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
};

// Test 1: Default C calling convention (works on all platforms)
TEST_F(CallingConventionTestFixture, DefaultCConvention) {
    const char *code = R"(
        void normalFunc(int x) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl *FD = findFunction(AST->getASTContext(), "normalFunc");
    ASSERT_NE(FD, nullptr) << "Function not found";
    ASSERT_EQ(getCallingConv(FD), CC_C) << "Expected CC_C";
}

// Test 2: Calling convention query API works
TEST_F(CallingConventionTestFixture, CallingConvQueryAPI) {
    const char *code = R"(
        void func1(int x) {}
        void __attribute__((ms_abi)) func2(int x) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl *func1 = findFunction(AST->getASTContext(), "func1");
    ASSERT_NE(func1, nullptr) << "func1 not found";

    // Verify we CAN query calling convention
    CallingConv cc1 = getCallingConv(func1);
    ASSERT_EQ(cc1, CC_C) << "func1 should have CC_C";
}

// Test 3: extern "C" preserves calling convention
TEST_F(CallingConventionTestFixture, ExternCPreservesCallingConv) {
    const char *code = R"(
        extern "C" void exported(int x) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl *FD = findFunction(AST->getASTContext(), "exported");
    ASSERT_NE(FD, nullptr) << "Function not found";
    ASSERT_TRUE(FD->isExternC()) << "Should have C linkage";

    // extern "C" functions still have calling convention (default CC_C)
    CallingConv CC = getCallingConv(FD);
    ASSERT_EQ(CC, CC_C) << "Expected CC_C for extern C function";
}
