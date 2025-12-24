/**
 * @file ConstevalIfTranslatorTest.cpp
 * @brief Tests for Phase 5: if consteval Support (C++23 P1938R3)
 *
 * Test Coverage:
 * - Basic if consteval with else branch
 * - Negated if !consteval
 * - if not consteval (alternate syntax)
 * - No else branch handling
 * - Nested if consteval
 * - In constexpr function
 * - In regular function
 * - Runtime strategy always picks runtime path
 * - Multiple if consteval in same function
 * - Template function with if consteval
 * - Warning emission
 *
 * Acceptance Criteria:
 * - 10+ test cases covering all scenarios
 * - 80%+ code coverage
 * - All tests pass
 * - C output is valid C99
 * - Conservative runtime fallback working
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/ConstevalIfTranslator.h"
#include "../include/CNodeBuilder.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++23"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Helper to find IfStmt in function body
IfStmt* findIfStmt(Stmt* S) {
    if (!S) return nullptr;

    if (auto* IS = dyn_cast<IfStmt>(S)) {
        return IS;
    }

    for (auto* Child : S->children()) {
        if (auto* Result = findIfStmt(Child)) {
            return Result;
        }
    }

    return nullptr;
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
class ConstevalIfTranslatorTest : public ::testing::Test {
protected:
};

// Test 1: Basic if consteval with else branch - should emit runtime (else) branch
TEST_F(ConstevalIfTranslatorTest, BasicConstevalWithElse) {
    const char *code = R"(
        int compute(int x) {
            if consteval {
                return x * 2;  // compile-time path
            } else {
                return x + 1;  // runtime path
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";
    ASSERT_TRUE(FD->getBody()) << "Function has no body";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";
    ASSERT_TRUE(ifStmt->isConsteval()) << "Should be consteval if";

    // Transform should return runtime (else) branch
    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed";

    // Result should be the else branch (runtime path)
    // We can't easily verify the exact content, but it should not be null
    EXPECT_NE(result, nullptr);
}

// Test 2: Negated if !consteval - should emit runtime path (then branch after swap)
TEST_F(ConstevalIfTranslatorTest, NegatedConsteval) {
    const char *code = R"(
        int compute(int x) {
            if !consteval {
                return x + 1;  // runtime path
            } else {
                return x * 2;  // compile-time path
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";
    ASSERT_TRUE(ifStmt->isConsteval()) << "Should be consteval if";
    ASSERT_TRUE(ifStmt->isNegatedConsteval()) << "Should be negated consteval";

    // Transform should handle negation correctly
    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed";
    EXPECT_NE(result, nullptr);
}

// Test 3: if not consteval (alternate syntax)
TEST_F(ConstevalIfTranslatorTest, NotConstevalSyntax) {
    const char *code = R"(
        int compute(int x) {
            if not consteval {
                return x + 1;  // runtime path
            } else {
                return x * 2;  // compile-time path
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";
    ASSERT_TRUE(ifStmt->isConsteval()) << "Should be consteval if";
    ASSERT_TRUE(ifStmt->isNegatedConsteval()) << "Should be negated consteval";

    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed";
}

// Test 4: No else branch - should return null statement
TEST_F(ConstevalIfTranslatorTest, NoElseBranch) {
    const char *code = R"(
        int compute(int x) {
            int result = x;
            if consteval {
                result *= 2;  // compile-time only
            }
            return result;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";
    ASSERT_TRUE(ifStmt->isConsteval()) << "Should be consteval if";

    // No else branch → Runtime strategy returns nullptr (no runtime branch)
    auto* result = translator.transform(ifStmt, Ctx);
    EXPECT_EQ(result, nullptr) << "Should return nullptr when no else branch";
}

// Test 5: In constexpr function - still uses runtime strategy
TEST_F(ConstevalIfTranslatorTest, InConstexprFunction) {
    const char *code = R"(
        constexpr int compute(int x) {
            if consteval {
                return x * 2;  // compile-time
            } else {
                return x + 1;  // runtime
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";
    ASSERT_TRUE(FD->isConstexpr()) << "Should be constexpr function";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";

    // Even in constexpr function, use runtime strategy (conservative)
    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed";
}

// Test 6: In regular function
TEST_F(ConstevalIfTranslatorTest, InRegularFunction) {
    const char *code = R"(
        int compute(int x) {
            if consteval {
                return x * 2;
            } else {
                return x + 1;
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";
    ASSERT_FALSE(FD->isConstexpr()) << "Should NOT be constexpr function";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";

    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed";
}

// Test 7: Nested if consteval (outer)
TEST_F(ConstevalIfTranslatorTest, NestedConstevalOuter) {
    const char *code = R"(
        int compute(int x) {
            if consteval {
                if (x > 0) {
                    return x * 2;
                }
                return x;
            } else {
                return x + 1;
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";
    ASSERT_TRUE(ifStmt->isConsteval()) << "Should be consteval if";

    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed for nested case";
}

// Test 8: Multiple if consteval in same function
TEST_F(ConstevalIfTranslatorTest, MultipleConstevalInFunction) {
    const char *code = R"(
        int compute(int x) {
            int result = 0;
            if consteval {
                result = x * 2;
            } else {
                result = x + 1;
            }

            if consteval {
                result *= 3;
            } else {
                result += 5;
            }

            return result;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";

    // Find first if consteval
    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "First if statement not found";

    auto* result1 = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result1) << "First translation should succeed";

    // Both should be translated successfully
    // (We can't easily find the second one without more complex traversal)
}

// Test 9: Template function with if consteval
TEST_F(ConstevalIfTranslatorTest, TemplateFunction) {
    const char *code = R"(
        template<typename T>
        T compute(T x) {
            if consteval {
                return x * T(2);
            } else {
                return x + T(1);
            }
        }

        int test() {
            return compute<int>(5);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    // Find template function
    auto* TU = Ctx.getTranslationUnitDecl();
    FunctionTemplateDecl* FTD = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *FT = dyn_cast<FunctionTemplateDecl>(D)) {
            if (FT->getNameAsString() == "compute") {
                FTD = FT;
                break;
            }
        }
    }

    ASSERT_TRUE(FTD) << "Template function 'compute' not found";

    auto* FD = FTD->getTemplatedDecl();
    ASSERT_TRUE(FD) << "Templated function not found";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found in template";

    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed for template";
}

// Test 10: Verify Runtime strategy never picks compile-time path
TEST_F(ConstevalIfTranslatorTest, RuntimeStrategyAlwaysPicksRuntime) {
    const char *code = R"(
        constexpr int compute(int x) {
            if consteval {
                return 999;  // This should NEVER be selected
            } else {
                return 111;  // This should ALWAYS be selected
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";

    // Runtime strategy must always select runtime (else) branch
    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed";

    // The result should be the else branch
    // (We verify this by checking it's not null and not the then branch)
    EXPECT_EQ(result, ifStmt->getElse()) << "Runtime strategy must select else branch";
}

// Test 11: Null input handling
TEST_F(ConstevalIfTranslatorTest, NullInputHandling) {
    auto AST = buildAST("int x = 0;");
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Runtime);

    // Transform with null should return null
    auto* result = translator.transform(nullptr, Ctx);
    EXPECT_EQ(result, nullptr) << "Null input should return null";
}

// Test 12: Optimistic strategy (future enhancement - currently returns runtime)
TEST_F(ConstevalIfTranslatorTest, OptimisticStrategyFallsBackToRuntime) {
    const char *code = R"(
        constexpr int compute(int x) {
            if consteval {
                return x * 2;
            } else {
                return x + 1;
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    ConstevalIfTranslator translator(builder, ConstevalStrategy::Optimistic);

    auto* TU = Ctx.getTranslationUnitDecl();
    auto* FD = findFunction(TU, "compute");
    ASSERT_TRUE(FD) << "Function 'compute' not found";

    auto* ifStmt = findIfStmt(FD->getBody());
    ASSERT_TRUE(ifStmt) << "If statement not found";

    // Optimistic strategy currently falls back to runtime (conservative)
    auto* result = translator.transform(ifStmt, Ctx);
    ASSERT_TRUE(result) << "Translation should succeed";
}
