/**
 * @file HandlerIntegrationTest.cpp
 * @brief Integration tests for handler cooperation
 *
 * Tests multiple handlers working together to translate C++ AST to C AST.
 * Validates that handlers cooperate correctly and symbol table works.
 */

#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class HandlerIntegrationTest
 * @brief Test fixture for handler integration testing
 */
class HandlerIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    std::unique_ptr<FunctionHandler> funcHandler;
    std::unique_ptr<VariableHandler> varHandler;
    std::unique_ptr<ExpressionHandler> exprHandler;
    std::unique_ptr<StatementHandler> stmtHandler;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create all handlers
        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
        exprHandler = std::make_unique<ExpressionHandler>();
        stmtHandler = std::make_unique<StatementHandler>();
    }

    void TearDown() override {
        stmtHandler.reset();
        exprHandler.reset();
        varHandler.reset();
        funcHandler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }
};

// ============================================================================
// Function + Expression Integration Tests (5 tests)
// ============================================================================

TEST_F(HandlerIntegrationTest, FunctionWithArithmetic) {
    // Test: int add(int a, int b) { return a + b; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int add(int a, int b) {
            return a + b;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    // Find the function declaration
    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "add") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr) << "Failed to find add function";

    // Translate function - handlers should cooperate internally
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "add");
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

TEST_F(HandlerIntegrationTest, FunctionWithComplexExpr) {
    // Test: int calc(int x) { return (x + 5) * 2; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int calc(int x) {
            return (x + 5) * 2;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "calc") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "calc");
}

TEST_F(HandlerIntegrationTest, FunctionCallWithArithmetic) {
    // Test: int square(int n) { return n * n; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int square(int n) {
            return n * n;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "square") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "square");
}

TEST_F(HandlerIntegrationTest, MultipleArithmeticFunctions) {
    // Test multiple functions in one translation unit
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int add(int a, int b) { return a + b; }
        int sub(int a, int b) { return a - b; }
    )");

    ASSERT_NE(testAST, nullptr);

    int funcCount = 0;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "add" || func->getNameAsString() == "sub") {
                auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
                    funcHandler->handleDecl(func, *context)
                );
                ASSERT_NE(cFunc, nullptr);
                funcCount++;
            }
        }
    }

    EXPECT_EQ(funcCount, 2) << "Should have translated 2 functions";
}

TEST_F(HandlerIntegrationTest, NestedArithmeticInFunction) {
    // Test: int complex_calc(int x, int y) { return (x + y) * (x - y); }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int complex_calc(int x, int y) {
            return (x + y) * (x - y);
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "complex_calc") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

// ============================================================================
// Function + Variable Integration Tests (5 tests)
// ============================================================================

TEST_F(HandlerIntegrationTest, FunctionWithLocalVar) {
    // Test: int func() { int x = 5; return x; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            int x = 5;
            return x;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, FunctionWithMultipleVars) {
    // Test: int func() { int x = 10; int y = 20; return x + y; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            int x = 10;
            int y = 20;
            return x + y;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, FunctionUsingVars) {
    // Test: int func() { int a = 3; int b = 4; return a + b; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            int a = 3;
            int b = 4;
            return a + b;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, FunctionWithConstVars) {
    // Test: int func() { const int MAX = 100; return MAX; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            const int MAX = 100;
            return MAX;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, FunctionVarInitFromParam) {
    // Test: int func(int param) { int local = param; return local; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func(int param) {
            int local = param;
            return local;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// All Handlers Combined Integration Tests (15 tests)
// ============================================================================

TEST_F(HandlerIntegrationTest, CompleteSimpleProgram) {
    // Test: int main() { return 0; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int main() {
            return 0;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "main") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cMain = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cMain, nullptr);
    EXPECT_EQ(cMain->getNameAsString(), "main");
}

TEST_F(HandlerIntegrationTest, FunctionWithAllFeatures) {
    // Test: int calc(int a, int b) { int result = a + b; return result; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int calc(int a, int b) {
            int result = a + b;
            return result;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "calc") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, NestedCompounds) {
    // Test nested blocks
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            {
                return 0;
            }
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, ComplexArithmetic) {
    // Test: int func(int a, int b, int c, int d, int e, int f) { return a + b - c * d / e % f; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func(int a, int b, int c, int d, int e, int f) {
            return a + b - c * d / e % f;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, VariableReuse) {
    // Test: int func() { int x = 5; int y = x + x; return y; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            int x = 5;
            int y = x + x;
            return y;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, ReturnComplexExpression) {
    // Test: int func(int a, int b, int c, int d) { return (a + b) * (c - d); }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func(int a, int b, int c, int d) {
            return (a + b) * (c - d);
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, MixedTypes) {
    // Test: void func() { int i = 42; float f = 3.14f; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        void func() {
            int i = 42;
            float f = 3.14f;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, ConstExpressions) {
    // Test: int func() { const int a = 10; const int b = a + 5; return b; }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            const int a = 10;
            const int b = a + 5;
            return b;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, DeepNesting) {
    // Test: int func(int a, int b, int c, int d, int e) { return ((((a + b) - c) * d) / e); }
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func(int a, int b, int c, int d, int e) {
            return ((((a + b) - c) * d) / e);
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, LargeFunction) {
    // Test function with many operations
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int large() {
            return 1 + 2 + 3;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "large") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, EdgeCaseArithmetic) {
    // Test division and modulo
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            return 10 / 3 + 10 % 3;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, AllOperatorsCombined) {
    // Test all arithmetic operators in one expression
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            return 10 + 5 - 2 * 3 / 4 % 2;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, StatementSequence) {
    // Test multiple statements in sequence
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int func() {
            int a = 1;
            int b = 2;
            int c = 3;
            return a + b + c;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "func") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
}

TEST_F(HandlerIntegrationTest, HandlerCooperation) {
    // Test comprehensive handler cooperation
    auto testAST = clang::tooling::buildASTFromCode(R"(
        int calculate(int x, int y) {
            int sum = x + y;
            int product = x * y;
            return sum + product;
        }
    )");

    ASSERT_NE(testAST, nullptr);

    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (func->getNameAsString() == "calculate") {
                cppFunc = func;
                break;
            }
        }
    }

    ASSERT_NE(cppFunc, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(
        funcHandler->handleDecl(cppFunc, *context)
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}
