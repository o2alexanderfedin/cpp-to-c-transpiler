/**
 * @file AutoDecayCopyTranslatorTest.cpp
 * @brief Tests for Phase 6: auto(x) Decay-Copy Translation (C++23 P0849R8)
 *
 * Test Coverage:
 * - auto(int&) → copy of int
 * - auto(const int&) → copy, remove const
 * - auto(int[10]) → decay to int*
 * - auto(void()) → decay to function pointer
 * - auto(int) → identity (already value)
 * - auto{x} → braced-init variant
 * - Multiple auto(x) in expression
 * - auto(x) with class types
 * - auto(x) in function call
 * - auto(x) in variable initialization
 *
 * Acceptance Criteria:
 * - 10+ test cases covering all scenarios
 * - 80%+ code coverage
 * - All tests pass
 * - C output is valid C99
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/AutoDecayCopyTranslator.h"
#include "../include/CNodeBuilder.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++23"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Helper to find CXXFunctionalCastExpr in AST
CXXFunctionalCastExpr* findFunctionalCast(Stmt* S) {
    if (!S) return nullptr;

    if (auto* FCE = dyn_cast<CXXFunctionalCastExpr>(S)) {
        // Check if it's auto(x) or auto{x}
        if (auto* AutoTy = dyn_cast<AutoType>(FCE->getTypeAsWritten().getTypePtr())) {
            return FCE;
        }
    }

    for (auto* Child : S->children()) {
        if (auto* Result = findFunctionalCast(Child)) {
            return Result;
        }
    }

    return nullptr;
}

// Test fixture
class AutoDecayCopyTranslatorTest : public ::testing::Test {
protected:
};

// Test 1: auto(int&) → copy of int
TEST_F(AutoDecayCopyTranslatorTest, ReferenceToValue) {
    const char *code = R"(
        int x = 42;
        int& ref = x;
        auto val = auto(ref);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(ref) expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "val") {
                if (auto* Init = VD->getInit()) {
                    autoExpr = findFunctionalCast(Init);
                    break;
                }
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(ref) expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is non-reference int
    QualType ResultType = Result->getType();
    EXPECT_FALSE(ResultType->isReferenceType()) << "Result should not be reference";
    EXPECT_TRUE(ResultType->isIntegerType()) << "Result should be int";
}

// Test 2: auto(const int&) → copy, remove const
TEST_F(AutoDecayCopyTranslatorTest, ConstReferenceToValue) {
    const char *code = R"(
        const int x = 42;
        const int& cref = x;
        auto val = auto(cref);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(cref) expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "val") {
                if (auto* Init = VD->getInit()) {
                    autoExpr = findFunctionalCast(Init);
                    break;
                }
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(cref) expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is non-const, non-reference int
    QualType ResultType = Result->getType();
    EXPECT_FALSE(ResultType->isReferenceType()) << "Result should not be reference";
    EXPECT_FALSE(ResultType.isConstQualified()) << "Result should not be const";
    EXPECT_TRUE(ResultType->isIntegerType()) << "Result should be int";
}

// Test 3: auto(int[10]) → decay to int*
TEST_F(AutoDecayCopyTranslatorTest, ArrayToPointer) {
    const char *code = R"(
        int arr[10];
        auto ptr = auto(arr);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(arr) expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "ptr") {
                if (auto* Init = VD->getInit()) {
                    autoExpr = findFunctionalCast(Init);
                    break;
                }
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(arr) expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is pointer to int
    QualType ResultType = Result->getType();
    EXPECT_TRUE(ResultType->isPointerType()) << "Result should be pointer";
    if (auto* PtrType = ResultType->getAs<PointerType>()) {
        EXPECT_TRUE(PtrType->getPointeeType()->isIntegerType())
            << "Pointee should be int";
    }
}

// Test 4: auto(void()) → decay to function pointer
TEST_F(AutoDecayCopyTranslatorTest, FunctionToPointer) {
    const char *code = R"(
        void func() {}
        auto fptr = auto(func);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(func) expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "fptr") {
                if (auto* Init = VD->getInit()) {
                    autoExpr = findFunctionalCast(Init);
                    break;
                }
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(func) expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is function pointer
    QualType ResultType = Result->getType();
    EXPECT_TRUE(ResultType->isPointerType()) << "Result should be pointer";
    if (auto* PtrType = ResultType->getAs<PointerType>()) {
        EXPECT_TRUE(PtrType->getPointeeType()->isFunctionType())
            << "Pointee should be function";
    }
}

// Test 5: auto(int) → identity (already value)
TEST_F(AutoDecayCopyTranslatorTest, ValueToValue) {
    const char *code = R"(
        int x = 42;
        auto val = auto(x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(x) expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "val") {
                if (auto* Init = VD->getInit()) {
                    autoExpr = findFunctionalCast(Init);
                    break;
                }
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(x) expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is int
    QualType ResultType = Result->getType();
    EXPECT_TRUE(ResultType->isIntegerType()) << "Result should be int";
    EXPECT_FALSE(ResultType->isReferenceType()) << "Result should not be reference";
}

// Test 6: auto{x} → braced-init variant
TEST_F(AutoDecayCopyTranslatorTest, BracedInit) {
    const char *code = R"(
        int x = 42;
        auto val = auto{x};
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto{x} expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "val") {
                if (auto* Init = VD->getInit()) {
                    autoExpr = findFunctionalCast(Init);
                    break;
                }
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto{x} expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is int
    QualType ResultType = Result->getType();
    EXPECT_TRUE(ResultType->isIntegerType()) << "Result should be int";
}

// Test 7: Multiple auto(x) in expression
TEST_F(AutoDecayCopyTranslatorTest, MultipleInExpression) {
    const char *code = R"(
        int x = 10;
        int y = 20;
        int& xref = x;
        int& yref = y;
        auto sum = auto(xref) + auto(yref);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find both auto() expressions
    auto* TU = Ctx.getTranslationUnitDecl();
    int autoCount = 0;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "sum") {
                if (auto* Init = VD->getInit()) {
                    // Count auto expressions recursively
                    std::function<void(Stmt*)> countAuto = [&](Stmt* S) {
                        if (!S) return;
                        if (auto* FCE = dyn_cast<CXXFunctionalCastExpr>(S)) {
                            if (auto* AutoTy = dyn_cast<AutoType>(
                                    FCE->getTypeAsWritten().getTypePtr())) {
                                autoCount++;
                            }
                        }
                        for (auto* Child : S->children()) {
                            countAuto(Child);
                        }
                    };
                    countAuto(Init);
                }
            }
        }
    }

    EXPECT_EQ(autoCount, 2) << "Should find 2 auto() expressions";
}

// Test 8: auto(x) with const qualified source
TEST_F(AutoDecayCopyTranslatorTest, ConstValueToValue) {
    const char *code = R"(
        const int x = 42;
        auto val = auto(x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(x) expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "val") {
                if (auto* Init = VD->getInit()) {
                    autoExpr = findFunctionalCast(Init);
                    break;
                }
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(x) expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is non-const int
    QualType ResultType = Result->getType();
    EXPECT_TRUE(ResultType->isIntegerType()) << "Result should be int";
    EXPECT_FALSE(ResultType.isConstQualified()) << "Result should not be const (decayed)";
}

// Test 9: auto(x) in function call
TEST_F(AutoDecayCopyTranslatorTest, InFunctionCall) {
    const char *code = R"(
        void func(int x) {}

        void test() {
            int& ref = *(new int(42));
            func(auto(ref));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(ref) expression in function call
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->hasBody()) {
                autoExpr = findFunctionalCast(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(ref) in function call";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type
    QualType ResultType = Result->getType();
    EXPECT_TRUE(ResultType->isIntegerType()) << "Result should be int";
    EXPECT_FALSE(ResultType->isReferenceType()) << "Result should not be reference";
}

// Test 10: Non-auto functional cast should return nullptr
TEST_F(AutoDecayCopyTranslatorTest, NonAutoFunctionalCast) {
    const char *code = R"(
        int x = 42;
        int val = int(x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the int(x) expression (not auto)
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* castExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "val") {
                if (auto* Init = VD->getInit()) {
                    if (auto* FCE = dyn_cast<CXXFunctionalCastExpr>(Init)) {
                        castExpr = FCE;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(castExpr, nullptr) << "Failed to find int(x) cast expression";

    // Transform should return nullptr for non-auto cast
    Expr* Result = translator.transform(castExpr, Ctx);
    EXPECT_EQ(Result, nullptr) << "Transform should return null for non-auto cast";
}

// Test 11: auto(x) with volatile qualifier
TEST_F(AutoDecayCopyTranslatorTest, VolatileReferenceToValue) {
    const char *code = R"(
        volatile int x = 42;
        volatile int& vref = x;
        auto val = auto(vref);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(vref) expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "val") {
                if (auto* Init = VD->getInit()) {
                    autoExpr = findFunctionalCast(Init);
                    break;
                }
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(vref) expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is non-volatile, non-reference int
    QualType ResultType = Result->getType();
    EXPECT_FALSE(ResultType->isReferenceType()) << "Result should not be reference";
    EXPECT_FALSE(ResultType.isVolatileQualified()) << "Result should not be volatile (decayed)";
    EXPECT_TRUE(ResultType->isIntegerType()) << "Result should be int";
}

// Test 12: auto(x) return type decay
TEST_F(AutoDecayCopyTranslatorTest, ReturnTypeDecay) {
    const char *code = R"(
        int& get_ref() {
            static int x = 42;
            return x;
        }

        void test() {
            auto val = auto(get_ref());
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    AutoDecayCopyTranslator translator(builder);

    // Find the auto(get_ref()) expression
    auto* TU = Ctx.getTranslationUnitDecl();
    CXXFunctionalCastExpr* autoExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->hasBody()) {
                autoExpr = findFunctionalCast(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(autoExpr, nullptr) << "Failed to find auto(get_ref()) expression";

    // Transform
    Expr* Result = translator.transform(autoExpr, Ctx);
    ASSERT_NE(Result, nullptr) << "Transform returned null";

    // Verify result type is int (not int&)
    QualType ResultType = Result->getType();
    EXPECT_FALSE(ResultType->isReferenceType()) << "Result should not be reference";
    EXPECT_TRUE(ResultType->isIntegerType()) << "Result should be int";
}
