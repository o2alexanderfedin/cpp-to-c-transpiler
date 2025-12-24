/**
 * @file ConstexprEnhancementTest.cpp
 * @brief Tests for Phase 6: Partial Constexpr Enhancement Support (C++23)
 *
 * Test Coverage:
 * - Simple constexpr with return literal
 * - Constexpr with arithmetic expressions
 * - Constexpr runtime fallback
 * - Non-constexpr function (skip)
 * - Complex constexpr (runtime fallback)
 * - Constexpr function call evaluation
 * - Compile-time evaluation success
 * - Warning emission for fallback
 *
 * Acceptance Criteria:
 * - 8+ test cases covering all scenarios
 * - Strategy determination accurate
 * - All tests pass
 * - Runtime fallback maintains correctness
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/ConstexprEnhancementHandler.h"
#include "../include/CNodeBuilder.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++23"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Helper to find function by name
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

// Test fixture
class ConstexprEnhancementTest : public ::testing::Test {
protected:
};

// Test 1: Simple constexpr with return literal → CompileTime
TEST_F(ConstexprEnhancementTest, SimpleReturnLiteral) {
    const char *code = R"(
        constexpr int answer() {
            return 42;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "answer");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'answer'";

    // Should be handled as constexpr
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Function should be handled as constexpr";

    // Strategy should be CompileTime
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::CompileTime)
        << "Simple literal return should use CompileTime strategy";
}

// Test 2: Constexpr with arithmetic → CompileTime
TEST_F(ConstexprEnhancementTest, ArithmeticExpression) {
    const char *code = R"(
        constexpr int compute() {
            return 10 + 32;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "compute");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'compute'";

    // Should be handled
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Function should be handled";

    // Strategy should be CompileTime (arithmetic with literals)
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::CompileTime)
        << "Arithmetic with literals should use CompileTime strategy";
}

// Test 3: Non-constexpr function → NotConstexpr
TEST_F(ConstexprEnhancementTest, NonConstexprFunction) {
    const char *code = R"(
        int regular() {
            return 42;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "regular");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'regular'";

    // Should NOT be handled (not constexpr)
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_FALSE(Handled) << "Non-constexpr function should not be handled";

    // Strategy should be NotConstexpr
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::NotConstexpr)
        << "Non-constexpr function should return NotConstexpr strategy";
}

// Test 4: Complex constexpr with loop → Runtime
TEST_F(ConstexprEnhancementTest, ComplexWithLoop) {
    const char *code = R"(
        constexpr int factorial(int n) {
            int result = 1;
            for (int i = 1; i <= n; i++) {
                result *= i;
            }
            return result;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "factorial");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'factorial'";

    // Should be handled
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Constexpr function should be handled";

    // Strategy should be Runtime (has parameters and loop)
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::Runtime)
        << "Complex constexpr with parameters should use Runtime strategy";
}

// Test 5: Constexpr with parameters → Runtime
TEST_F(ConstexprEnhancementTest, WithParameters) {
    const char *code = R"(
        constexpr int add(int a, int b) {
            return a + b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "add");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'add'";

    // Should be handled
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Constexpr function should be handled";

    // Strategy should be Runtime (has parameters)
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::Runtime)
        << "Constexpr with parameters should use Runtime strategy";
}

// Test 6: Constexpr with multiple statements → Runtime
TEST_F(ConstexprEnhancementTest, MultipleStatements) {
    const char *code = R"(
        constexpr int compute() {
            int x = 10;
            int y = 32;
            return x + y;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "compute");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'compute'";

    // Should be handled
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Constexpr function should be handled";

    // Strategy should be Runtime (multiple statements)
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::Runtime)
        << "Constexpr with multiple statements should use Runtime strategy";
}

// Test 7: Constexpr returning bool literal
TEST_F(ConstexprEnhancementTest, BoolLiteral) {
    const char *code = R"(
        constexpr bool is_valid() {
            return true;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "is_valid");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'is_valid'";

    // Should be handled
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Constexpr function should be handled";

    // Strategy should be CompileTime
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::CompileTime)
        << "Bool literal return should use CompileTime strategy";
}

// Test 8: Constexpr with negative literal
TEST_F(ConstexprEnhancementTest, NegativeLiteral) {
    const char *code = R"(
        constexpr int negative() {
            return -42;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "negative");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'negative'";

    // Should be handled
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Constexpr function should be handled";

    // Strategy should be CompileTime (unary operator on literal)
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::CompileTime)
        << "Negative literal should use CompileTime strategy";
}

// Test 9: Constexpr returning floating point
TEST_F(ConstexprEnhancementTest, FloatingPointLiteral) {
    const char *code = R"(
        constexpr double pi() {
            return 3.14159;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "pi");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'pi'";

    // Should be handled
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Constexpr function should be handled";

    // Strategy should be CompileTime
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::CompileTime)
        << "Floating point literal should use CompileTime strategy";
}

// Test 10: Constexpr with parenthesized expression
TEST_F(ConstexprEnhancementTest, ParenthesizedExpression) {
    const char *code = R"(
        constexpr int compute() {
            return (40 + 2);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstexprEnhancementHandler handler(builder);

    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionDecl* FD = findFunction(TU, "compute");
    ASSERT_NE(FD, nullptr) << "Failed to find function 'compute'";

    // Should be handled
    bool Handled = handler.handleConstexprFunction(FD, Ctx);
    EXPECT_TRUE(Handled) << "Constexpr function should be handled";

    // Strategy should be CompileTime
    ConstexprStrategy Strategy = handler.determineStrategy(FD, Ctx);
    EXPECT_EQ(Strategy, ConstexprStrategy::CompileTime)
        << "Parenthesized literal expression should use CompileTime strategy";
}
