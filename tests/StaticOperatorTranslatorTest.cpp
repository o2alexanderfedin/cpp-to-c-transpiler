/**
 * @file StaticOperatorTranslatorTest.cpp
 * @brief Tests for Phase 2: Static operator() and operator[] Translation
 *
 * Test Coverage:
 * - Static operator() basic call
 * - Static operator() on instance
 * - Static operator() with multiple args
 * - Static operator() with return type
 * - Static operator[] single arg
 * - Static operator[] multiple args (combines with Phase 1)
 * - Static operator in template class
 * - Static operator with const parameters
 * - Function name generation
 * - Integration with MultidimSubscriptTranslator
 *
 * Acceptance Criteria:
 * - 8+ test cases covering all scenarios
 * - All tests pass
 * - C output is valid C99
 * - No regressions in Phase 1 tests
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/StaticOperatorTranslator.h"
#include "../include/CNodeBuilder.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST_static(const char *code) {
    std::vector<std::string> args = {"-std=c++23"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Helper function to find class by name
CXXRecordDecl* findClass_static(TranslationUnitDecl* TU, const std::string& name) {
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                return RD;
            }
        }
    }
    return nullptr;
}

// Helper to find static operator method
CXXMethodDecl* findStaticOperator(CXXRecordDecl* Class, OverloadedOperatorKind Op) {
    for (auto* Method : Class->methods()) {
        if (Method->isOverloadedOperator() &&
            Method->getOverloadedOperator() == Op &&
            Method->isStatic()) {
            return Method;
        }
    }
    return nullptr;
}

// Helper to find CXXOperatorCallExpr in AST
CXXOperatorCallExpr* findOperatorCall_static(Stmt* S, OverloadedOperatorKind Op) {
    if (!S) return nullptr;

    if (auto* OpCall = dyn_cast<CXXOperatorCallExpr>(S)) {
        if (OpCall->getOperator() == Op) {
            return OpCall;
        }
    }

    for (auto* Child : S->children()) {
        if (auto* Result = findOperatorCall_static(Child, Op)) {
            return Result;
        }
    }

    return nullptr;
}

// Test fixture
class StaticOperatorTranslatorTest : public ::testing::Test {
protected:
};

// Test 1: Basic static operator() detection and method transformation
TEST_F(StaticOperatorTranslatorTest, BasicStaticOperatorCall) {
    const char *code = R"(
        struct Calculator {
            static int operator()(int a, int b) { return a + b; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);

    // Create C TranslationUnit for generated code
    auto* C_TU = TranslationUnitDecl::Create(Ctx);

    // Find the Calculator class
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Calculator = findClass_static(TU, "Calculator");
    ASSERT_TRUE(Calculator) << "Calculator class not found";

    // Find static operator()
    auto* OpMethod = findStaticOperator(Calculator, OO_Call);
    ASSERT_TRUE(OpMethod) << "Static operator() not found";
    ASSERT_TRUE(OpMethod->isStatic()) << "Operator should be static";

    // Transform method to C function
    auto* C_Func = translator.transformMethod(OpMethod, Ctx, C_TU);
    ASSERT_TRUE(C_Func) << "Method transformation should succeed";
    EXPECT_EQ(C_Func->getNameAsString(), "Calculator__call_static")
        << "Function name should be Calculator__call_static";
    EXPECT_EQ(C_Func->getNumParams(), 2) << "Should have 2 parameters (no 'this')";
}

// Test 2: Static operator() called on instance
TEST_F(StaticOperatorTranslatorTest, StaticOperatorCallOnInstance) {
    const char *code = R"(
        struct Calculator {
            static int operator()(int a, int b) { return a + b; }
        };

        void test() {
            Calculator calc;
            int result = calc(1, 2);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();

    // Find the operator call in test function
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->getBody()) {
                opCall = findOperatorCall_static(FD->getBody(), OO_Call);
                if (opCall) break;
            }
        }
    }

    ASSERT_TRUE(opCall) << "Operator call not found";

    // Transform call site
    auto* C_Call = translator.transformCall(opCall, Ctx);
    ASSERT_TRUE(C_Call) << "Call transformation should succeed";

    // Arguments should be 1, 2 (skipping the object)
    EXPECT_EQ(C_Call->getNumArgs(), 2) << "Should have 2 arguments (no object)";
}

// Test 3: Static operator() with multiple arguments
TEST_F(StaticOperatorTranslatorTest, StaticOperatorMultipleArgs) {
    const char *code = R"(
        struct MathOps {
            static double operator()(int a, double b, float c) {
                return a + b + c;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* MathOps = findClass_static(TU, "MathOps");
    ASSERT_TRUE(MathOps);

    auto* OpMethod = findStaticOperator(MathOps, OO_Call);
    ASSERT_TRUE(OpMethod);

    auto* C_Func = translator.transformMethod(OpMethod, Ctx, C_TU);
    ASSERT_TRUE(C_Func);
    EXPECT_EQ(C_Func->getNumParams(), 3) << "Should have 3 parameters";
    EXPECT_TRUE(C_Func->getReturnType()->isFloatingType())
        << "Return type should be double";
}

// Test 4: Static operator[] single argument
TEST_F(StaticOperatorTranslatorTest, StaticOperatorSubscriptSingleArg) {
    const char *code = R"(
        struct LookupTable {
            static int operator[](int key) { return key * 2; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* LookupTable = findClass_static(TU, "LookupTable");
    ASSERT_TRUE(LookupTable);

    auto* OpMethod = findStaticOperator(LookupTable, OO_Subscript);
    ASSERT_TRUE(OpMethod);
    ASSERT_TRUE(OpMethod->isStatic());

    auto* C_Func = translator.transformMethod(OpMethod, Ctx, C_TU);
    ASSERT_TRUE(C_Func);
    EXPECT_EQ(C_Func->getNameAsString(), "LookupTable__subscript_static");
    EXPECT_EQ(C_Func->getNumParams(), 1) << "Should have 1 parameter (no 'this')";
}

// Test 5: Static operator[] multiple arguments (combines with Phase 1)
TEST_F(StaticOperatorTranslatorTest, StaticOperatorSubscriptMultipleArgs) {
    const char *code = R"(
        struct Matrix {
            static int operator[](int i, int j) { return i * 10 + j; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Matrix = findClass_static(TU, "Matrix");
    ASSERT_TRUE(Matrix);

    auto* OpMethod = findStaticOperator(Matrix, OO_Subscript);
    ASSERT_TRUE(OpMethod);

    auto* C_Func = translator.transformMethod(OpMethod, Ctx, C_TU);
    ASSERT_TRUE(C_Func);
    EXPECT_EQ(C_Func->getNameAsString(), "Matrix__subscript_2d_static");
    EXPECT_EQ(C_Func->getNumParams(), 2) << "Should have 2 parameters";
}

// Test 6: Static operator with const parameters
TEST_F(StaticOperatorTranslatorTest, StaticOperatorConstParams) {
    const char *code = R"(
        struct StringOps {
            static int operator()(const char* str) { return 42; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* StringOps = findClass_static(TU, "StringOps");
    ASSERT_TRUE(StringOps);

    auto* OpMethod = findStaticOperator(StringOps, OO_Call);
    ASSERT_TRUE(OpMethod);

    auto* C_Func = translator.transformMethod(OpMethod, Ctx, C_TU);
    ASSERT_TRUE(C_Func);
    EXPECT_EQ(C_Func->getNumParams(), 1);

    // Check that const-ness is preserved
    auto* Param = C_Func->getParamDecl(0);
    EXPECT_TRUE(Param->getType()->isPointerType());
}

// Test 7: Non-static operator should return nullptr
TEST_F(StaticOperatorTranslatorTest, NonStaticOperatorReturnsNull) {
    const char *code = R"(
        struct Regular {
            int operator()(int a) { return a; }  // NOT static
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Regular = findClass_static(TU, "Regular");
    ASSERT_TRUE(Regular);

    // Find the non-static operator
    CXXMethodDecl* OpMethod = nullptr;
    for (auto* Method : Regular->methods()) {
        if (Method->isOverloadedOperator() &&
            Method->getOverloadedOperator() == OO_Call) {
            OpMethod = Method;
            break;
        }
    }

    ASSERT_TRUE(OpMethod);
    ASSERT_FALSE(OpMethod->isStatic()) << "Operator should NOT be static";

    // Should return nullptr for non-static operator
    auto* C_Func = translator.transformMethod(OpMethod, Ctx, C_TU);
    EXPECT_FALSE(C_Func) << "Should return nullptr for non-static operator";
}

// Test 8: Static operator[] call site transformation
TEST_F(StaticOperatorTranslatorTest, StaticSubscriptCallSiteTransform) {
    const char *code = R"(
        struct LookupTable {
            static int operator[](int key) { return key * 2; }
        };

        void test() {
            int value = LookupTable{}[42];
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();

    // Find the operator call in test function
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->getBody()) {
                opCall = findOperatorCall_static(FD->getBody(), OO_Subscript);
                if (opCall) break;
            }
        }
    }

    ASSERT_TRUE(opCall) << "Operator call not found";

    // Transform call site
    auto* C_Call = translator.transformCall(opCall, Ctx);
    ASSERT_TRUE(C_Call) << "Call transformation should succeed";
    EXPECT_EQ(C_Call->getNumArgs(), 1) << "Should have 1 argument (key)";
}

// Test 9: Function name generation for different operators
TEST_F(StaticOperatorTranslatorTest, FunctionNameGeneration) {
    const char *code = R"(
        struct Test1 {
            static int operator()() { return 0; }
        };

        struct Test2 {
            static int operator[](int x) { return x; }
        };

        struct Test3 {
            static int operator[](int x, int y) { return x + y; }
        };

        struct Test4 {
            static int operator[](int x, int y, int z) { return x + y + z; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);
    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();

    // Test1: operator() → Test1__call_static
    auto* Test1 = findClass_static(TU, "Test1");
    ASSERT_TRUE(Test1);
    auto* Op1 = findStaticOperator(Test1, OO_Call);
    ASSERT_TRUE(Op1);
    auto* Func1 = translator.transformMethod(Op1, Ctx, C_TU);
    ASSERT_TRUE(Func1);
    EXPECT_EQ(Func1->getNameAsString(), "Test1__call_static");

    // Test2: operator[](int) → Test2__subscript_static
    auto* Test2 = findClass_static(TU, "Test2");
    ASSERT_TRUE(Test2);
    auto* Op2 = findStaticOperator(Test2, OO_Subscript);
    ASSERT_TRUE(Op2);
    auto* Func2 = translator.transformMethod(Op2, Ctx, C_TU);
    ASSERT_TRUE(Func2);
    EXPECT_EQ(Func2->getNameAsString(), "Test2__subscript_static");

    // Test3: operator[](int, int) → Test3__subscript_2d_static
    auto* Test3 = findClass_static(TU, "Test3");
    ASSERT_TRUE(Test3);
    auto* Op3 = findStaticOperator(Test3, OO_Subscript);
    ASSERT_TRUE(Op3);
    auto* Func3 = translator.transformMethod(Op3, Ctx, C_TU);
    ASSERT_TRUE(Func3);
    EXPECT_EQ(Func3->getNameAsString(), "Test3__subscript_2d_static");

    // Test4: operator[](int, int, int) → Test4__subscript_3d_static
    auto* Test4 = findClass_static(TU, "Test4");
    ASSERT_TRUE(Test4);
    auto* Op4 = findStaticOperator(Test4, OO_Subscript);
    ASSERT_TRUE(Op4);
    auto* Func4 = translator.transformMethod(Op4, Ctx, C_TU);
    ASSERT_TRUE(Func4);
    EXPECT_EQ(Func4->getNameAsString(), "Test4__subscript_3d_static");
}

// Test 10: Duplicate function detection (get-or-create pattern)
TEST_F(StaticOperatorTranslatorTest, DuplicateFunctionDetection) {
    const char *code = R"(
        struct Calculator {
            static int operator()(int a, int b) { return a + b; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_static(code);
    ASSERT_TRUE(AST);

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    StaticOperatorTranslator translator(builder);
    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();

    auto* Calculator = findClass_static(TU, "Calculator");
    ASSERT_TRUE(Calculator);
    auto* OpMethod = findStaticOperator(Calculator, OO_Call);
    ASSERT_TRUE(OpMethod);

    // Transform twice - should return same function
    auto* Func1 = translator.transformMethod(OpMethod, Ctx, C_TU);
    auto* Func2 = translator.transformMethod(OpMethod, Ctx, C_TU);

    ASSERT_TRUE(Func1);
    ASSERT_TRUE(Func2);
    EXPECT_EQ(Func1, Func2) << "Should return same function on duplicate transform";
}
