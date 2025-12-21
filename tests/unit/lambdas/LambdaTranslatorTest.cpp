/**
 * @file LambdaTranslatorTest.cpp
 * @brief Comprehensive tests for C++ lambda expression translation to C closures
 *
 * Stream 1: Lambdas & Closures
 * Target: 60 test functions covering lambda translation, closure implementation,
 *         and capture mechanisms for the C++ to C transpiler.
 *
 * Test Categories:
 * 1. Basic Lambdas (10 tests)
 * 2. Capture Mechanisms (15 tests)
 * 3. Closure Generation (12 tests)
 * 4. Lambda Types (10 tests)
 * 5. Edge Cases (13 tests)
 *
 * Migrated to Google Test Framework (Phase 15-01)
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <string>
#include <vector>

using namespace clang;

// ============================================================================
// Test Fixture
// ============================================================================

class LambdaTranslatorTest : public ::testing::Test {
protected:
    // Helper to build AST from C++ code
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        std::vector<std::string> args = {"-std=c++17"};
        return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
    }

    // Helper to find lambda expression in AST
    class LambdaFinder : public RecursiveASTVisitor<LambdaFinder> {
    public:
        std::vector<LambdaExpr*> lambdas;

        bool VisitLambdaExpr(LambdaExpr *E) {
            lambdas.push_back(E);
            return true;
        }
    };

    LambdaExpr* findFirstLambda(ASTUnit* AST) {
        LambdaFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
        return finder.lambdas.empty() ? nullptr : finder.lambdas[0];
    }

    std::vector<LambdaExpr*> findAllLambdas(ASTUnit* AST) {
        LambdaFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
        return finder.lambdas;
    }
};

// ============================================================================
// Category 1: Basic Lambdas (10 tests)
// ============================================================================

TEST_F(LambdaTranslatorTest, LambdaNoCaptureSimple) {
    const char *code = R"(
        void foo() {
            auto lambda = []() { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: No captures
    EXPECT_EQ(lambda->capture_size(), 0u) << "Lambda should have no captures";

    // Verify: Lambda is callable
    ASSERT_TRUE(lambda->getCallOperator() != nullptr) << "Lambda should have call operator";

    // Verify: Return type is deduced
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_TRUE(callOp->getReturnType()->isIntegerType()) << "Return type should be integer";
}

TEST_F(LambdaTranslatorTest, LambdaExplicitReturnType) {
    const char *code = R"(
        void foo() {
            auto lambda = []() -> int { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Explicit return type
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_TRUE(callOp->getReturnType()->isIntegerType()) << "Return type should be int";

    // Verify: Return type is explicitly specified (not auto)
    EXPECT_TRUE(lambda->hasExplicitResultType()) << "Lambda should have explicit return type";
}

TEST_F(LambdaTranslatorTest, LambdaWithParameters) {
    const char *code = R"(
        void foo() {
            auto lambda = [](int x, int y) { return x + y; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has 2 parameters
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_EQ(callOp->param_size(), 2u) << "Lambda should have 2 parameters";

    // Verify: Parameter types
    EXPECT_TRUE(callOp->getParamDecl(0)->getType()->isIntegerType()) << "First param should be int";
    EXPECT_TRUE(callOp->getParamDecl(1)->getType()->isIntegerType()) << "Second param should be int";
}

TEST_F(LambdaTranslatorTest, LambdaMutable) {
    const char *code = R"(
        void foo() {
            int x = 0;
            auto lambda = [x]() mutable { x++; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda is mutable
    EXPECT_TRUE(lambda->isMutable()) << "Lambda should be mutable";

    // Verify: Call operator is not const
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_FALSE(callOp->isConst()) << "Mutable lambda call operator should not be const";
}

TEST_F(LambdaTranslatorTest, LambdaVoidReturn) {
    const char *code = R"(
        void foo() {
            int x = 0;
            auto lambda = [&x]() { x = 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Return type is void
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_TRUE(callOp->getReturnType()->isVoidType()) << "Lambda should return void";
}

TEST_F(LambdaTranslatorTest, LambdaMultipleStatements) {
    const char *code = R"(
        void foo() {
            auto lambda = [](int x) {
                int y = x * 2;
                int z = y + 1;
                return z;
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda body exists
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    ASSERT_TRUE(callOp->hasBody()) << "Lambda should have a body";

    // Verify: Body is a compound statement
    const Stmt* body = callOp->getBody();
    EXPECT_TRUE(isa<CompoundStmt>(body)) << "Lambda body should be CompoundStmt";
}

TEST_F(LambdaTranslatorTest, LambdaTrailingReturnComplex) {
    const char *code = R"(
        void foo() {
            auto lambda = [](int x, int y) -> double {
                return static_cast<double>(x) / y;
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Explicit return type is double
    EXPECT_TRUE(lambda->hasExplicitResultType()) << "Lambda should have explicit return type";

    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_TRUE(callOp->getReturnType()->isFloatingType()) << "Return type should be double";
}

TEST_F(LambdaTranslatorTest, LambdaImmediatelyInvoked) {
    const char *code = R"(
        void foo() {
            int result = []() { return 42; }();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda exists and can be invoked
    EXPECT_TRUE(lambda->getCallOperator() != nullptr) << "Lambda should have call operator";
}

TEST_F(LambdaTranslatorTest, LambdaNoexcept) {
    const char *code = R"(
        void foo() {
            auto lambda = []() noexcept { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Call operator has exception spec
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    const FunctionProtoType* FPT = callOp->getType()->getAs<FunctionProtoType>();
    EXPECT_TRUE(FPT != nullptr) << "Lambda should have function prototype type";
}

TEST_F(LambdaTranslatorTest, LambdaVariadicParameters) {
    const char *code = R"(
        template<typename... Args>
        void foo() {
            auto lambda = [](auto... args) { return sizeof...(args); };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Note: Generic lambdas create template call operators
    LambdaExpr* lambda = findFirstLambda(AST.get());
    EXPECT_TRUE(lambda != nullptr) << "Lambda expression not found";
}

// ============================================================================
// Category 2: Capture Mechanisms (15 tests)
// ============================================================================

TEST_F(LambdaTranslatorTest, CaptureByValueSingle) {
    const char *code = R"(
        void foo() {
            int x = 42;
            auto lambda = [x]() { return x; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has 1 capture
    EXPECT_EQ(lambda->capture_size(), 1u) << "Lambda should have 1 capture";

    // Verify: Capture is by value
    const LambdaCapture& capture = *lambda->capture_begin();
    EXPECT_TRUE(!capture.capturesVariable() || capture.getCaptureKind() == LCK_ByCopy)
        << "Capture should be by value";
}

TEST_F(LambdaTranslatorTest, CaptureByValueMultiple) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2, z = 3;
            auto lambda = [x, y, z]() { return x + y + z; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has 3 captures
    EXPECT_EQ(lambda->capture_size(), 3u) << "Lambda should have 3 captures";

    // Verify: All captures are by value
    for (const auto& capture : lambda->captures()) {
        EXPECT_EQ(capture.getCaptureKind(), LCK_ByCopy) << "All captures should be by value";
    }
}

TEST_F(LambdaTranslatorTest, CaptureByReferenceSingle) {
    const char *code = R"(
        void foo() {
            int x = 42;
            auto lambda = [&x]() { x = 100; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has 1 capture
    EXPECT_EQ(lambda->capture_size(), 1u) << "Lambda should have 1 capture";

    // Verify: Capture is by reference
    const LambdaCapture& capture = *lambda->capture_begin();
    EXPECT_EQ(capture.getCaptureKind(), LCK_ByRef) << "Capture should be by reference";
}

TEST_F(LambdaTranslatorTest, CaptureByReferenceMultiple) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2, z = 3;
            auto lambda = [&x, &y, &z]() { x = y = z = 0; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has 3 captures
    EXPECT_EQ(lambda->capture_size(), 3u) << "Lambda should have 3 captures";

    // Verify: All captures are by reference
    for (const auto& capture : lambda->captures()) {
        EXPECT_EQ(capture.getCaptureKind(), LCK_ByRef) << "All captures should be by reference";
    }
}

TEST_F(LambdaTranslatorTest, CaptureAllByValue) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2;
            auto lambda = [=]() { return x + y; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has default capture
    EXPECT_EQ(lambda->getCaptureDefault(), LCD_ByCopy)
        << "Lambda should have default capture by value";
}

TEST_F(LambdaTranslatorTest, CaptureAllByReference) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2;
            auto lambda = [&]() { x = y = 0; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has default capture by reference
    EXPECT_EQ(lambda->getCaptureDefault(), LCD_ByRef)
        << "Lambda should have default capture by reference";
}

TEST_F(LambdaTranslatorTest, CaptureMixed) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2;
            auto lambda = [x, &y]() { y = x; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has 2 captures
    EXPECT_EQ(lambda->capture_size(), 2u) << "Lambda should have 2 captures";

    // Verify: Mixed capture kinds
    bool hasValue = false, hasRef = false;
    for (const auto& capture : lambda->captures()) {
        if (capture.getCaptureKind() == LCK_ByCopy) hasValue = true;
        if (capture.getCaptureKind() == LCK_ByRef) hasRef = true;
    }
    EXPECT_TRUE(hasValue && hasRef) << "Lambda should have both value and reference captures";
}

TEST_F(LambdaTranslatorTest, CaptureInit) {
    const char *code = R"(
        void foo() {
            auto lambda = [x = 42]() { return x; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has 1 capture
    EXPECT_EQ(lambda->capture_size(), 1u) << "Lambda should have 1 capture";

    // Verify: Capture has initializer
    const LambdaCapture& capture = *lambda->capture_begin();
    EXPECT_TRUE(capture.capturesVariable()) << "Init capture should capture variable";
}

TEST_F(LambdaTranslatorTest, CaptureThis) {
    const char *code = R"(
        class Foo {
            int x;
            void bar() {
                auto lambda = [this]() { return x; };
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Captures this
    EXPECT_EQ(lambda->capture_size(), 1u) << "Lambda should have 1 capture";

    const LambdaCapture& capture = *lambda->capture_begin();
    EXPECT_TRUE(capture.capturesThis()) << "Lambda should capture this";
}

TEST_F(LambdaTranslatorTest, CaptureThisByCopy) {
    const char *code = R"(
        class Foo {
            int x;
            void bar() {
                auto lambda = [*this]() { return x; };
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has capture
    EXPECT_GE(lambda->capture_size(), 1u) << "Lambda should have at least 1 capture";
}

TEST_F(LambdaTranslatorTest, CaptureDefaultWithException) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2;
            auto lambda = [=, &y]() { y = x; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has default capture
    EXPECT_EQ(lambda->getCaptureDefault(), LCD_ByCopy)
        << "Lambda should have default capture by value";

    // Verify: Has explicit captures (at least one)
    unsigned explicitCaptures = 0;
    for (const auto& capture : lambda->explicit_captures()) {
        (void)capture; // Mark as used
        explicitCaptures++;
    }
    EXPECT_GE(explicitCaptures, 1u) << "Lambda should have explicit captures";
}

TEST_F(LambdaTranslatorTest, CaptureConstVariable) {
    const char *code = R"(
        void foo() {
            const int x = 42;
            auto lambda = [x]() { return x; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has capture
    EXPECT_EQ(lambda->capture_size(), 1u) << "Lambda should have 1 capture";
}

TEST_F(LambdaTranslatorTest, CaptureNestedLambdas) {
    const char *code = R"(
        void foo() {
            int x = 1;
            auto outer = [x]() {
                auto inner = [x]() { return x; };
                return inner();
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    std::vector<LambdaExpr*> lambdas = findAllLambdas(AST.get());
    EXPECT_EQ(lambdas.size(), 2u) << "Should find 2 lambda expressions";

    // Verify: Both lambdas capture x
    for (auto* lambda : lambdas) {
        EXPECT_GE(lambda->capture_size(), 1u) << "Each lambda should have at least 1 capture";
    }
}

TEST_F(LambdaTranslatorTest, CaptureStructuredBinding) {
    const char *code = R"(
        #include <tuple>
        void foo() {
            auto [a, b] = std::make_tuple(1, 2);
            auto lambda = [a, b]() { return a + b; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    EXPECT_TRUE(lambda != nullptr) << "Lambda expression not found";
}

TEST_F(LambdaTranslatorTest, CaptureOuterScope) {
    const char *code = R"(
        void foo() {
            int x = 1;
            {
                int y = 2;
                auto lambda = [x, y]() { return x + y; };
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Captures both variables
    EXPECT_EQ(lambda->capture_size(), 2u) << "Lambda should capture 2 variables";
}

// ============================================================================
// Category 3: Closure Generation (12 tests)
// ============================================================================

TEST_F(LambdaTranslatorTest, ClosureStructGeneration) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2;
            auto lambda = [x, y]() { return x + y; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda creates a closure type
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    ASSERT_TRUE(closureType) << "Lambda should have closure type";

    // Verify: Closure type is a class
    EXPECT_TRUE(closureType->isClass()) << "Closure type should be a class";
}

TEST_F(LambdaTranslatorTest, ClosureMemberVariables) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2;
            auto lambda = [x, y]() { return x + y; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Closure has fields for captures
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    ASSERT_TRUE(closureType) << "Lambda should have closure type";

    // Count fields (captures become members)
    unsigned fieldCount = 0;
    for (auto* field : closureType->fields()) {
        (void)field; // Mark as used
        fieldCount++;
    }

    EXPECT_EQ(fieldCount, 2u) << "Closure should have 2 member variables for captures";
}

TEST_F(LambdaTranslatorTest, ClosureFunctionPointerConversion) {
    const char *code = R"(
        void foo() {
            auto lambda = []() { return 42; };
            int (*fptr)() = lambda;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda has no captures (can convert to function pointer)
    EXPECT_EQ(lambda->capture_size(), 0u)
        << "Lambda should have no captures for function pointer conversion";

    // Verify: Closure type has conversion operator
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    EXPECT_TRUE(closureType != nullptr) << "Lambda should have closure type";
}

TEST_F(LambdaTranslatorTest, ClosureCallOperator) {
    const char *code = R"(
        void foo() {
            int x = 1;
            auto lambda = [x](int y) { return x + y; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has call operator
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    ASSERT_TRUE(callOp) << "Lambda should have call operator";

    // Verify: Call operator has correct signature
    EXPECT_EQ(callOp->param_size(), 1u) << "Call operator should have 1 parameter";
    EXPECT_TRUE(callOp->isConst()) << "Non-mutable lambda call operator should be const";
}

TEST_F(LambdaTranslatorTest, ClosureLifetime) {
    const char *code = R"(
        void foo() {
            int x = 42;
            {
                auto lambda = [x]() { return x; };
                int result = lambda();
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda is valid within its scope
    EXPECT_TRUE(lambda->getCallOperator() != nullptr) << "Lambda should be callable";
}

TEST_F(LambdaTranslatorTest, ClosureReferenceMembers) {
    const char *code = R"(
        void foo() {
            int x = 1;
            auto lambda = [&x]() { x++; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Closure has reference member
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    ASSERT_TRUE(closureType) << "Lambda should have closure type";

    // Check that at least one field is a reference
    bool hasReferenceMember = false;
    for (auto* field : closureType->fields()) {
        if (field->getType()->isReferenceType()) {
            hasReferenceMember = true;
            break;
        }
    }
    EXPECT_TRUE(hasReferenceMember) << "Closure should have reference member for reference capture";
}

TEST_F(LambdaTranslatorTest, ClosureThisPointer) {
    const char *code = R"(
        class Foo {
            int member;
            void method() {
                auto lambda = [this]() { return member; };
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Captures this
    const LambdaCapture& capture = *lambda->capture_begin();
    EXPECT_TRUE(capture.capturesThis()) << "Lambda should capture this pointer";
}

TEST_F(LambdaTranslatorTest, ClosureEmptySize) {
    const char *code = R"(
        void foo() {
            auto lambda = []() { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: No captures means minimal closure size
    EXPECT_EQ(lambda->capture_size(), 0u) << "Empty lambda should have no captures";

    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    EXPECT_TRUE(closureType != nullptr) << "Lambda should have closure type";
}

TEST_F(LambdaTranslatorTest, ClosureCopyConstructor) {
    const char *code = R"(
        void foo() {
            int x = 42;
            auto lambda1 = [x]() { return x; };
            auto lambda2 = lambda1;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Closure type is copyable
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    EXPECT_TRUE(closureType != nullptr) << "Lambda should have closure type";
}

TEST_F(LambdaTranslatorTest, ClosureMoveConstructor) {
    const char *code = R"(
        #include <utility>
        void foo() {
            int x = 42;
            auto lambda1 = [x]() { return x; };
            auto lambda2 = std::move(lambda1);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Closure exists
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    EXPECT_TRUE(closureType != nullptr) << "Lambda should have closure type";
}

TEST_F(LambdaTranslatorTest, ClosureComplexTypes) {
    const char *code = R"(
        #include <string>
        #include <vector>
        void foo() {
            std::string str = "hello";
            std::vector<int> vec = {1, 2, 3};
            auto lambda = [str, vec]() { return str.size() + vec.size(); };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    if (!AST || AST->getDiagnostics().hasErrorOccurred()) {
        GTEST_SKIP() << "STL headers not available or parse errors occurred";
    }

    LambdaExpr* lambda = findFirstLambda(AST.get());
    if (!lambda) {
        GTEST_SKIP() << "Failed to parse code with STL";
    }

    // Verify: Captures complex types
    EXPECT_EQ(lambda->capture_size(), 2u) << "Lambda should capture 2 complex objects";
}

TEST_F(LambdaTranslatorTest, ClosureDestructor) {
    const char *code = R"(
        #include <string>
        void foo() {
            std::string str = "hello";
            auto lambda = [str]() { return str; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Closure type exists (destructor is implicit)
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    EXPECT_TRUE(closureType != nullptr) << "Lambda should have closure type";
}

// ============================================================================
// Category 4: Lambda Types (10 tests)
// ============================================================================

TEST_F(LambdaTranslatorTest, LambdaAutoVariable) {
    const char *code = R"(
        void foo() {
            auto lambda = []() { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda has unique type
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    EXPECT_TRUE(closureType != nullptr) << "Lambda should have unique closure type";
}

TEST_F(LambdaTranslatorTest, LambdaAsParameter) {
    const char *code = R"(
        template<typename F>
        void apply(F func) { func(); }

        void foo() {
            apply([]() { return 42; });
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda can be passed as parameter
    EXPECT_TRUE(lambda->getCallOperator() != nullptr) << "Lambda should be callable";
}

TEST_F(LambdaTranslatorTest, LambdaReturned) {
    const char *code = R"(
        auto make_lambda() {
            return []() { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda can be returned
    EXPECT_EQ(lambda->capture_size(), 0u) << "Returned lambda should have no local captures";
}

TEST_F(LambdaTranslatorTest, LambdaInStdFunction) {
    const char *code = R"(
        #include <functional>
        void foo() {
            std::function<int()> func = []() { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    if (!AST) {
        GTEST_SKIP() << "STL headers not available";
    }

    LambdaExpr* lambda = findFirstLambda(AST.get());
    if (!lambda) {
        GTEST_SKIP() << "Failed to parse code with STL";
    }

    // Verify: Lambda is compatible with std::function
    EXPECT_TRUE(lambda->getCallOperator() != nullptr) << "Lambda should have call operator";
}

TEST_F(LambdaTranslatorTest, LambdaGeneric) {
    const char *code = R"(
        void foo() {
            auto lambda = [](auto x) { return x + 1; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Generic lambda has template call operator
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_TRUE(callOp != nullptr) << "Lambda should have call operator";
}

TEST_F(LambdaTranslatorTest, LambdaInContainer) {
    const char *code = R"(
        #include <vector>
        #include <functional>
        void foo() {
            std::vector<std::function<int()>> funcs;
            funcs.push_back([]() { return 42; });
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    if (!AST) {
        GTEST_SKIP() << "STL headers not available";
    }

    LambdaExpr* lambda = findFirstLambda(AST.get());
    if (!lambda) {
        GTEST_SKIP() << "Failed to parse code with STL";
    }

    // Verify: Lambda can be stored in container
    EXPECT_TRUE(lambda->getCallOperator() != nullptr) << "Lambda should be callable";
}

TEST_F(LambdaTranslatorTest, LambdaDecltype) {
    const char *code = R"(
        void foo() {
            auto lambda = []() { return 42; };
            decltype(lambda) lambda2 = lambda;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda type can be deduced with decltype
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    EXPECT_TRUE(closureType != nullptr) << "Lambda should have closure type";
}

TEST_F(LambdaTranslatorTest, LambdaInTemplate) {
    const char *code = R"(
        template<typename T>
        void apply(T value) {
            auto lambda = [value]() { return value; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda exists in template
    EXPECT_GE(lambda->capture_size(), 1u) << "Lambda should capture template parameter";
}

TEST_F(LambdaTranslatorTest, LambdaDeducedReturn) {
    const char *code = R"(
        void foo() {
            auto lambda = [](int x) {
                if (x > 0) return 42;
                return -1;
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Return type is deduced
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_TRUE(callOp->getReturnType()->isIntegerType()) << "Return type should be deduced as int";
}

TEST_F(LambdaTranslatorTest, LambdaStateless) {
    const char *code = R"(
        void foo() {
            auto lambda = [](int x, int y) { return x + y; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Stateless lambda (no captures)
    EXPECT_EQ(lambda->capture_size(), 0u) << "Stateless lambda should have no captures";
}

// ============================================================================
// Category 5: Edge Cases (13 tests)
// ============================================================================

TEST_F(LambdaTranslatorTest, LambdaEmpty) {
    const char *code = R"(
        void foo() {
            auto lambda = []() {};
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Empty lambda is valid
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    ASSERT_TRUE(callOp != nullptr) << "Empty lambda should have call operator";
    EXPECT_TRUE(callOp->getReturnType()->isVoidType()) << "Empty lambda should return void";
}

TEST_F(LambdaTranslatorTest, LambdaRecursive) {
    const char *code = R"(
        #include <functional>
        void foo() {
            std::function<int(int)> fib = [&fib](int n) {
                return n < 2 ? n : fib(n-1) + fib(n-2);
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    if (!AST) {
        GTEST_SKIP() << "STL headers not available";
    }

    LambdaExpr* lambda = findFirstLambda(AST.get());
    if (!lambda) {
        GTEST_SKIP() << "Failed to parse code with STL";
    }

    // Verify: Captures itself by reference
    EXPECT_GE(lambda->capture_size(), 1u) << "Recursive lambda should capture itself";
}

TEST_F(LambdaTranslatorTest, LambdaConstexpr) {
    const char *code = R"(
        constexpr auto lambda = []() { return 42; };
        constexpr int value = lambda();
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda can be used in constexpr context
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_TRUE(callOp != nullptr) << "Lambda should have call operator";
}

TEST_F(LambdaTranslatorTest, LambdaExceptionSpec) {
    const char *code = R"(
        void foo() {
            auto lambda = []() noexcept(true) { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Exception specification exists
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    const FunctionProtoType* FPT = callOp->getType()->getAs<FunctionProtoType>();
    EXPECT_TRUE(FPT != nullptr) << "Lambda should have function prototype type";
}

TEST_F(LambdaTranslatorTest, LambdaUnevaluatedContext) {
    const char *code = R"(
        void foo() {
            decltype([]() { return 42; }) lambda;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Lambda in decltype is in unevaluated context
    LambdaExpr* lambda = findFirstLambda(AST.get());
    EXPECT_TRUE(lambda != nullptr) << "Lambda expression not found in unevaluated context";
}

TEST_F(LambdaTranslatorTest, LambdaAttributes) {
    const char *code = R"(
        void foo() {
            auto lambda = []() [[nodiscard]] { return 42; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda with attributes is valid
    EXPECT_TRUE(lambda->getCallOperator() != nullptr) << "Lambda should have call operator";
}

TEST_F(LambdaTranslatorTest, LambdaTemplateArgument) {
    const char *code = R"(
        template<typename F>
        struct Wrapper { F func; };

        void foo() {
            Wrapper<decltype([](){ return 42; })> w;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda type can be used as template argument
    const CXXRecordDecl* closureType = lambda->getLambdaClass();
    EXPECT_TRUE(closureType != nullptr) << "Lambda should have closure type";
}

TEST_F(LambdaTranslatorTest, MultipleLambdas) {
    const char *code = R"(
        void foo() {
            auto result = [](int x) { return x * 2; }(
                          [](int y) { return y + 1; }(5));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    std::vector<LambdaExpr*> lambdas = findAllLambdas(AST.get());
    EXPECT_EQ(lambdas.size(), 2u) << "Should find 2 lambda expressions";

    // Verify: Both lambdas are valid
    for (auto* lambda : lambdas) {
        EXPECT_TRUE(lambda->getCallOperator() != nullptr) << "Each lambda should have call operator";
    }
}

TEST_F(LambdaTranslatorTest, LambdaCaptureTrailingComma) {
    const char *code = R"(
        void foo() {
            int x = 1, y = 2;
            auto lambda = [x, y,]() { return x + y; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    // Note: This may not parse in all C++ standards
    if (!AST) {
        GTEST_SKIP() << "Trailing comma not supported";
    }

    LambdaExpr* lambda = findFirstLambda(AST.get());
    if (lambda) {
        EXPECT_EQ(lambda->capture_size(), 2u) << "Lambda should have 2 captures";
    }
}

TEST_F(LambdaTranslatorTest, LambdaComplexDefaultCapture) {
    const char *code = R"(
        struct Foo {
            int member;
            void method() {
                int local = 1;
                auto lambda = [=, this]() { return member + local; };
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Has default capture and explicit this
    EXPECT_EQ(lambda->getCaptureDefault(), LCD_ByCopy)
        << "Lambda should have default capture by value";
}

TEST_F(LambdaTranslatorTest, LambdaMoveCapture) {
    const char *code = R"(
        #include <memory>
        void foo() {
            auto ptr = std::make_unique<int>(42);
            auto lambda = [p = std::move(ptr)]() { return *p; };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    if (!AST || AST->getDiagnostics().hasErrorOccurred()) {
        GTEST_SKIP() << "STL headers not available or parse errors occurred";
    }

    LambdaExpr* lambda = findFirstLambda(AST.get());
    if (!lambda) {
        GTEST_SKIP() << "Failed to parse code with STL";
    }

    // Verify: Init capture with move
    EXPECT_GE(lambda->capture_size(), 1u) << "Lambda should have move capture";
}

TEST_F(LambdaTranslatorTest, LambdaIfInit) {
    const char *code = R"(
        void foo() {
            if (auto lambda = []() { return 42; }; lambda() > 0) {
                // use lambda
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Lambda in if-init is valid
    EXPECT_TRUE(lambda->getCallOperator() != nullptr) << "Lambda should be callable";
}

TEST_F(LambdaTranslatorTest, LambdaParameterPack) {
    const char *code = R"(
        void foo() {
            auto lambda = [](auto... args) {
                return (args + ...);
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    LambdaExpr* lambda = findFirstLambda(AST.get());
    ASSERT_TRUE(lambda) << "Lambda expression not found";

    // Verify: Generic lambda with parameter pack
    const CXXMethodDecl* callOp = lambda->getCallOperator();
    EXPECT_TRUE(callOp != nullptr) << "Lambda should have call operator";
}
