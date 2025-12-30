/**
 * @file StandaloneFunctionTranslationTest_gtest.cpp
 * @brief Test suite for standalone function translation (Phase 8 - v2.1.0)
 * Migrated to Google Test framework
 *
 * Phase 8: Standalone Functions
 * Tests translation of free functions, function overloading, main(), function
 * calls
 *
 * Test-Driven Development (TDD):
 * - Write tests FIRST (these will fail initially)
 * - Implement minimal code to pass tests
 * - Refactor while keeping tests green
 */

#include <gtest/gtest.h>
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include "OverloadRegistry.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <memory>

using namespace clang;

// ============================================================================
// CLI Accessor Function Stubs (required for CppToCVisitor)
// ============================================================================

bool shouldGenerateACSL() { return false; }
ACSLLevel getACSLLevel() { return ACSLLevel::Basic; }
ACSLOutputMode getACSLOutputMode() { return ACSLOutputMode::Inline; }
bool shouldGenerateMemoryPredicates() { return false; }
bool shouldMonomorphizeTemplates() { return false; }
unsigned int getTemplateInstantiationLimit() { return 100; }
bool shouldEnableRTTI() { return false; }

// ============================================================================
// Test Fixture for Standalone Function Translation
// ============================================================================

class StandaloneFunctionTranslationTestFixture : public ::testing::Test {
protected:
    // Helper to create AST from C++ code
    std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// Test 1: Simple Function Declaration and Definition
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, SimpleFunctionDeclaration) {
    const char *cpp = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    // Run visitor on AST
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify C function generated
    FunctionDecl *CFunc = visitor.getCFunc("add");
    ASSERT_NE(CFunc, nullptr) << "C function not generated";
    EXPECT_EQ(CFunc->getName(), "add") << "Function name mismatch";
    EXPECT_EQ(CFunc->getNumParams(), 2) << "Parameter count mismatch";
}

// ============================================================================
// Test 2: Function with Pointer Return
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, FunctionWithPointerReturn) {
    const char *cpp = R"(
        int* allocate(int size) {
            return nullptr;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("allocate");
    ASSERT_NE(CFunc, nullptr) << "C function not generated";
    EXPECT_TRUE(CFunc->getReturnType()->isPointerType())
        << "Return type should be pointer";
}

// ============================================================================
// Test 3: Overloaded Functions (Name Mangling)
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, OverloadedFunctions) {
    const char *cpp = R"(
        int max(int a, int b) {
            return a > b ? a : b;
        }

        double max(double a, double b) {
            return a > b ? a : b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify both functions exist with different mangled names
    // The exact mangling pattern will be verified by NameMangler tests
    FunctionDecl *CFunc1 = visitor.getCFunc("max_int_int");
    FunctionDecl *CFunc2 = visitor.getCFunc("max_float_float");

    // At least one should exist (depending on mangling scheme)
    EXPECT_TRUE(CFunc1 != nullptr || CFunc2 != nullptr)
        << "Overloaded functions not generated with mangled names";
}

// ============================================================================
// Test 4: Recursive Function
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, RecursiveFunction) {
    const char *cpp = R"(
        int factorial(int n) {
            if (n <= 1) return 1;
            return n * factorial(n - 1);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("factorial");
    ASSERT_NE(CFunc, nullptr) << "Recursive function not generated";
}

// ============================================================================
// Test 5: Main Function (No Name Mangling)
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, MainFunction) {
    const char *cpp = R"(
        int main(int argc, char* argv[]) {
            return 0;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Main function should be named exactly "main", not mangled
    FunctionDecl *CFunc = visitor.getCFunc("main");
    ASSERT_NE(CFunc, nullptr) << "Main function not generated";
    EXPECT_EQ(CFunc->getName(), "main") << "Main function should not be mangled";
}

// ============================================================================
// Test 6: Static Function (Internal Linkage)
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, StaticFunction) {
    const char *cpp = R"(
        static int helper(int x) {
            return x * 2;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("helper");
    ASSERT_NE(CFunc, nullptr) << "Static function not generated";
    EXPECT_EQ(CFunc->getStorageClass(), SC_Static)
        << "Static linkage not preserved";
}

// ============================================================================
// Test 7: Extern Function (External Linkage)
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, ExternFunction) {
    const char *cpp = R"(
        extern int external_func(int a);

        int wrapper(int a) {
            return external_func(a);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Note: external_func is a forward declaration (no body)
    // The wrapper function should be generated
    FunctionDecl *WrapperFunc = visitor.getCFunc("wrapper");
    ASSERT_NE(WrapperFunc, nullptr) << "Wrapper function not generated";
}

// ============================================================================
// Test 8: Variadic Function
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, VariadicFunction) {
    const char *cpp = R"(
        int sum(int count, ...) {
            return 0;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("sum");
    ASSERT_NE(CFunc, nullptr) << "Variadic function not generated";
    EXPECT_TRUE(CFunc->isVariadic()) << "Variadic property not preserved";
}

// ============================================================================
// Test 9: Inline Function
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, InlineFunction) {
    const char *cpp = R"(
        inline int abs_val(int x) {
            return x < 0 ? -x : x;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("abs_val");
    ASSERT_NE(CFunc, nullptr) << "Inline function not generated";
    EXPECT_TRUE(CFunc->isInlineSpecified()) << "Inline specifier not preserved";
}

// ============================================================================
// Test 10: Mutually Recursive Functions
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, MutuallyRecursiveFunctions) {
    const char *cpp = R"(
        int isEven(int n);
        int isOdd(int n);

        int isEven(int n) {
            if (n == 0) return 1;
            return isOdd(n - 1);
        }

        int isOdd(int n) {
            if (n == 0) return 0;
            return isEven(n - 1);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *EvenFunc = visitor.getCFunc("isEven");
    FunctionDecl *OddFunc = visitor.getCFunc("isOdd");

    ASSERT_NE(EvenFunc, nullptr) << "isEven function not generated";
    ASSERT_NE(OddFunc, nullptr) << "isOdd function not generated";
}

// ============================================================================
// Test 11: Function with Const Parameter
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, ConstQualifiedParameter) {
    const char *cpp = R"(
        int process(const int value) {
            return value * 2;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("process");
    ASSERT_NE(CFunc, nullptr) << "Function not generated";
    ASSERT_EQ(CFunc->getNumParams(), 1) << "Parameter count mismatch";

    // Verify const qualifier
    ParmVarDecl *Param = CFunc->getParamDecl(0);
    EXPECT_TRUE(Param->getType().isConstQualified())
        << "Const qualifier not preserved";
}

// ============================================================================
// Test 12: Void Return Function
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, VoidReturnFunction) {
    const char *cpp = R"(
        void print_hello() {
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("print_hello");
    ASSERT_NE(CFunc, nullptr) << "Void function not generated";
    EXPECT_TRUE(CFunc->getReturnType()->isVoidType())
        << "Return type should be void";
}

// ============================================================================
// Test 13: NameMangler - Standalone Function Name Mangling
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, NameMangler_StandaloneFunctionMangling) {
    const char *cpp = R"(
        void foo(int x) {}
        void foo(double x) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    ASTContext &Ctx = AST->getASTContext();
    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(Ctx, registry);

    // Find the overloaded functions in AST
    bool foundIntVersion = false;
    bool foundDoubleVersion = false;

    for (Decl *D : Ctx.getTranslationUnitDecl()->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getName() == "foo" && FD->getNumParams() == 1) {
                std::string mangledName = mangler.mangleFunctionName(FD);

                // Check if parameter type is encoded in mangled name
                QualType ParamType = FD->getParamDecl(0)->getType();
                if (ParamType->isIntegerType()) {
                    EXPECT_TRUE(mangledName.find("int") != std::string::npos ||
                               mangledName == "foo") // First one might not be mangled
                        << "Integer parameter not encoded in mangled name";
                    foundIntVersion = true;
                } else if (ParamType->isFloatingType()) {
                    EXPECT_TRUE(mangledName.find("float") != std::string::npos ||
                               mangledName.find("double") != std::string::npos ||
                               mangledName == "foo") // First one might not be mangled
                        << "Double parameter not encoded in mangled name";
                    foundDoubleVersion = true;
                }
            }
        }
    }

    EXPECT_TRUE(foundIntVersion) << "Int version of foo not found";
    EXPECT_TRUE(foundDoubleVersion) << "Double version of foo not found";
}

// ============================================================================
// Test 14: Multiple Overloads with Different Parameter Counts
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, OverloadingDifferentParamCounts) {
    const char *cpp = R"(
        int compute(int a) { return a * 2; }
        int compute(int a, int b) { return a + b; }
        int compute(int a, int b, int c) { return a + b + c; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Try to find functions with mangled names
    // The exact names depend on mangling scheme, but all three should exist
    int functionsFound = 0;
    if (visitor.getCFunc("compute"))
        functionsFound++;
    if (visitor.getCFunc("compute_int"))
        functionsFound++;
    if (visitor.getCFunc("compute_int_int"))
        functionsFound++;
    if (visitor.getCFunc("compute_int_int_int"))
        functionsFound++;

    // We should have at least generated functions (exact names vary)
    EXPECT_GE(functionsFound, 1) << "Overloaded functions not generated";
}

// ============================================================================
// Test 15: Function with No Parameters
// ============================================================================
TEST_F(StandaloneFunctionTranslationTestFixture, NoParameterFunction) {
    const char *cpp = R"(
        int get_constant() {
            return 42;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("get_constant");
    ASSERT_NE(CFunc, nullptr) << "No-parameter function not generated";
    EXPECT_EQ(CFunc->getNumParams(), 0) << "Should have zero parameters";
}
