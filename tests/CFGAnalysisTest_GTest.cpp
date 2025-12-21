// tests/CFGAnalysisTest_GTest.cpp
// Migrated from CFGAnalysisTest.cpp to Google Test framework
// Story #151: CFG (Control Flow Graph) Analysis Infrastructure

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "../include/CFGAnalyzer.h"

using namespace clang;

// Test fixture for CFG Analysis tests
class CFGAnalysisTestFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }

    FunctionDecl* findFunction(TranslationUnitDecl *TU, const std::string &name) {
        for (auto *D : TU->decls()) {
            if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
                if (Func->getNameAsString() == name) {
                    return Func;
                }
            }
        }
        return nullptr;
    }
};

// Test 1: CFG detects all return statements
TEST_F(CFGAnalysisTestFixture, CFGDetectsAllReturns) {
    const char *Code = R"(
        void func(int flag) {
            int x = 10;
            if (flag) {
                return;  // Early return
            }
            int y = 20;
            return;  // Normal return
        }
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "func");
    ASSERT_NE(FD, nullptr) << "Function 'func' not found";

    // Build CFG and analyze
    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 2 exit points (2 return statements)
    ASSERT_EQ(analyzer.getExitPointCount(), 2) << "Expected 2 exit points";
}

// Test 2: CFG tracks local variable declarations
TEST_F(CFGAnalysisTestFixture, CFGTracksLocalVars) {
    const char *Code = R"(
        void func() {
            int x = 10;
            int y = 20;
            float z = 3.14f;
        }
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "func");
    ASSERT_NE(FD, nullptr) << "Function 'func' not found";

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 3 local variables
    ASSERT_EQ(analyzer.getLocalVarCount(), 3) << "Expected 3 local variables";
}

// Test 3: CFG identifies nested scopes
TEST_F(CFGAnalysisTestFixture, CFGIdentifiesNestedScopes) {
    const char *Code = R"(
        void func() {
            int x = 10;
            {
                int y = 20;
                {
                    int z = 30;
                }
            }
        }
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "func");
    ASSERT_NE(FD, nullptr) << "Function 'func' not found";

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 3 scopes (function body + 2 nested compound statements)
    ASSERT_EQ(analyzer.getScopeCount(), 3) << "Expected 3 scopes";
}

// Test 4: CFG detects break/continue statements
TEST_F(CFGAnalysisTestFixture, CFGDetectsBreakContinue) {
    const char *Code = R"(
        void func(int count) {
            for (int i = 0; i < count; ++i) {
                if (i == 5) break;
                if (i == 3) continue;
            }
        }
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "func");
    ASSERT_NE(FD, nullptr) << "Function 'func' not found";

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: CFG should detect break and continue
    ASSERT_EQ(analyzer.getBreakContinueCount(), 2) << "Expected 2 break/continue statements";
}

// Test 5: CFG detects goto statements
TEST_F(CFGAnalysisTestFixture, CFGDetectsGoto) {
    const char *Code = R"(
        void func(int flag) {
            int x = 10;
            if (flag) {
                goto cleanup;
            }
            int y = 20;
        cleanup:
            return;
        }
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "func");
    ASSERT_NE(FD, nullptr) << "Function 'func' not found";

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: CFG should detect goto
    ASSERT_EQ(analyzer.getGotoCount(), 1) << "Expected 1 goto statement";
}
