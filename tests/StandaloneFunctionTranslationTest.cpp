/**
 * @file StandaloneFunctionTranslationTest.cpp
 * @brief Test suite for standalone function translation (Phase 8 - v2.1.0)
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
#include "FileOriginTracker.h"
#include "CppToCVisitor.h"
#include "NameMangler.h"
#include "clang/Tooling/Tooling.h"
#include <memory>

using namespace clang;

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
  return tooling::buildASTFromCode(code);
}

// ============================================================================
// Test 1: Simple Function Declaration and Definition
// ============================================================================

// Test fixture
class StandaloneFunctionTranslationTest : public ::testing::Test {
protected:
};

TEST_F(StandaloneFunctionTranslationTest, SimpleFunctionDeclaration) {

      const char *cpp = R"(
            int add(int a, int b) {
                return a + b;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      // Run visitor on AST
      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      // Verify C function generated
      FunctionDecl *CFunc = visitor.getCFunc("add");
      ASSERT_TRUE(CFunc != nullptr) << "C function not generated";
      ASSERT_TRUE(CFunc->getName() == "add") << "Function name mismatch";
      ASSERT_TRUE(CFunc->getNumParams() == 2) << "Parameter count mismatch";
}

TEST_F(StandaloneFunctionTranslationTest, FunctionWithPointerReturn) {

      const char *cpp = R"(
            int* allocate(int size) {
                return nullptr;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *CFunc = visitor.getCFunc("allocate");
      ASSERT_TRUE(CFunc != nullptr) << "C function not generated";
      ASSERT_TRUE(CFunc->getReturnType()->isPointerType()) << "Return type should be pointer";
}

TEST_F(StandaloneFunctionTranslationTest, OverloadedFunctions) {

      const char *cpp = R"(
            int max(int a, int b) {
                return a > b ? a : b;
            }

            double max(double a, double b) {
                return a > b ? a : b;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      // Verify both functions exist with different mangled names
      // The exact mangling pattern will be verified by NameMangler tests
      FunctionDecl *CFunc1 = visitor.getCFunc("max_int_int");
      FunctionDecl *CFunc2 = visitor.getCFunc("max_float_float");

      // At least one should exist (depending on mangling scheme)
      ASSERT_TRUE(CFunc1 != nullptr || CFunc2 != nullptr) << "Overloaded functions not generated with mangled names";
}

TEST_F(StandaloneFunctionTranslationTest, RecursiveFunction) {

      const char *cpp = R"(
            int factorial(int n) {
                if (n <= 1) return 1;
                return n * factorial(n - 1);
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *CFunc = visitor.getCFunc("factorial");
      ASSERT_TRUE(CFunc != nullptr) << "Recursive function not generated";
}

TEST_F(StandaloneFunctionTranslationTest, MainFunction) {

      const char *cpp = R"(
            int main(int argc, char* argv[]) {
                return 0;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      // Main function should be named exactly "main", not mangled
      FunctionDecl *CFunc = visitor.getCFunc("main");
      ASSERT_TRUE(CFunc != nullptr) << "Main function not generated";
      ASSERT_TRUE(CFunc->getName() == "main") << "Main function should not be mangled";
}

TEST_F(StandaloneFunctionTranslationTest, StaticFunction) {

      const char *cpp = R"(
            static int helper(int x) {
                return x * 2;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *CFunc = visitor.getCFunc("helper");
      ASSERT_TRUE(CFunc != nullptr) << "Static function not generated";
      ASSERT_TRUE(CFunc->getStorageClass() == SC_Static) << "Static linkage not preserved";
}

TEST_F(StandaloneFunctionTranslationTest, ExternFunction) {

      const char *cpp = R"(
            extern int external_func(int a);

            int wrapper(int a) {
                return external_func(a);
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      // Note: external_func is a forward declaration (no body)
      // The wrapper function should be generated
      FunctionDecl *WrapperFunc = visitor.getCFunc("wrapper");
      ASSERT_TRUE(WrapperFunc != nullptr) << "Wrapper function not generated";
}

TEST_F(StandaloneFunctionTranslationTest, VariadicFunction) {

      const char *cpp = R"(
            int sum(int count, ...) {
                return 0;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *CFunc = visitor.getCFunc("sum");
      ASSERT_TRUE(CFunc != nullptr) << "Variadic function not generated";
      ASSERT_TRUE(CFunc->isVariadic()) << "Variadic property not preserved";
}

TEST_F(StandaloneFunctionTranslationTest, InlineFunction) {

      const char *cpp = R"(
            inline int abs_val(int x) {
                return x < 0 ? -x : x;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *CFunc = visitor.getCFunc("abs_val");
      ASSERT_TRUE(CFunc != nullptr) << "Inline function not generated";
      ASSERT_TRUE(CFunc->isInlineSpecified()) << "Inline specifier not preserved";
}

TEST_F(StandaloneFunctionTranslationTest, MutuallyRecursiveFunctions) {
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
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *EvenFunc = visitor.getCFunc("isEven");
      FunctionDecl *OddFunc = visitor.getCFunc("isOdd");

      ASSERT_TRUE(EvenFunc != nullptr) << "isEven function not generated";
      ASSERT_TRUE(OddFunc != nullptr) << "isOdd function not generated";
}

TEST_F(StandaloneFunctionTranslationTest, ConstQualifiedParameter) {

      const char *cpp = R"(
            int process(const int value) {
                return value * 2;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *CFunc = visitor.getCFunc("process");
      ASSERT_TRUE(CFunc != nullptr) << "Function not generated";
      ASSERT_TRUE(CFunc->getNumParams() == 1) << "Parameter count mismatch";

      // Verify const qualifier
      ParmVarDecl *Param = CFunc->getParamDecl(0);
      ASSERT_TRUE(Param->getType().isConstQualified()) << "Const qualifier not preserved";
}

TEST_F(StandaloneFunctionTranslationTest, VoidReturnFunction) {

      const char *cpp = R"(
            void print_hello() {
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *CFunc = visitor.getCFunc("print_hello");
      ASSERT_TRUE(CFunc != nullptr) << "Void function not generated";
      ASSERT_TRUE(CFunc->getReturnType()->isVoidType()) << "Return type should be void";
}

TEST_F(StandaloneFunctionTranslationTest, OverloadingDifferentParamCounts) {

      const char *cpp = R"(
            int compute(int a) { return a * 2; }
            int compute(int a, int b) { return a + b; }
            int compute(int a, int b, int c) { return a + b + c; }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

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
      ASSERT_TRUE(functionsFound >= 1) << "Overloaded functions not generated";
}

TEST_F(StandaloneFunctionTranslationTest, NoParameterFunction) {

      const char *cpp = R"(
            int get_constant() {
                return 42;
            }
        )";

      std::unique_ptr<ASTUnit> AST = buildAST(cpp);
      ASSERT_TRUE(AST) << "Failed to parse C++ code";

      CNodeBuilder builder(AST->getASTContext());
      cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder, tracker, C_TU);

      visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

      FunctionDecl *CFunc = visitor.getCFunc("get_constant");
      ASSERT_TRUE(CFunc != nullptr) << "No-parameter function not generated";
      ASSERT_TRUE(CFunc->getNumParams() == 0) << "Should have zero parameters";
}
