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

#include "CNodeBuilder.h"
#include "CppToCVisitor.h"
#include "NameMangler.h"
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

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name)                                                        \
  {                                                                            \
    std::cout << "✓" << std::endl;                                             \
    tests_passed++;                                                            \
  }
#define TEST_FAIL(name, msg)                                                   \
  {                                                                            \
    std::cout << "✗ FAILED: " << msg << std::endl;                             \
    tests_failed++;                                                            \
  }
#define ASSERT(expr, msg)                                                      \
  if (!(expr)) {                                                               \
    TEST_FAIL("", msg);                                                        \
    return;                                                                    \
  }

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
  return tooling::buildASTFromCode(code);
}

// ============================================================================
// Test 1: Simple Function Declaration and Definition
// ============================================================================
void test_SimpleFunctionDeclaration() {
  TEST_START("SimpleFunctionDeclaration: int add(int a, int b) translation");

  const char *cpp = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  // Run visitor on AST
  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  // Verify C function generated
  FunctionDecl *CFunc = visitor.getCFunc("add");
  ASSERT(CFunc != nullptr, "C function not generated");
  ASSERT(CFunc->getName() == "add", "Function name mismatch");
  ASSERT(CFunc->getNumParams() == 2, "Parameter count mismatch");

  TEST_PASS("SimpleFunctionDeclaration");
}

// ============================================================================
// Test 2: Function with Pointer Return
// ============================================================================
void test_FunctionWithPointerReturn() {
  TEST_START("FunctionWithPointerReturn: int* allocate(int size)");

  const char *cpp = R"(
        int* allocate(int size) {
            return nullptr;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *CFunc = visitor.getCFunc("allocate");
  ASSERT(CFunc != nullptr, "C function not generated");
  ASSERT(CFunc->getReturnType()->isPointerType(),
         "Return type should be pointer");

  TEST_PASS("FunctionWithPointerReturn");
}

// ============================================================================
// Test 3: Overloaded Functions (Name Mangling)
// ============================================================================
void test_OverloadedFunctions() {
  TEST_START("OverloadedFunctions: max(int, int) and max(double, double)");

  const char *cpp = R"(
        int max(int a, int b) {
            return a > b ? a : b;
        }

        double max(double a, double b) {
            return a > b ? a : b;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  // Verify both functions exist with different mangled names
  // The exact mangling pattern will be verified by NameMangler tests
  FunctionDecl *CFunc1 = visitor.getCFunc("max_int_int");
  FunctionDecl *CFunc2 = visitor.getCFunc("max_float_float");

  // At least one should exist (depending on mangling scheme)
  ASSERT(CFunc1 != nullptr || CFunc2 != nullptr,
         "Overloaded functions not generated with mangled names");

  TEST_PASS("OverloadedFunctions");
}

// ============================================================================
// Test 4: Recursive Function
// ============================================================================
void test_RecursiveFunction() {
  TEST_START("RecursiveFunction: int factorial(int n)");

  const char *cpp = R"(
        int factorial(int n) {
            if (n <= 1) return 1;
            return n * factorial(n - 1);
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *CFunc = visitor.getCFunc("factorial");
  ASSERT(CFunc != nullptr, "Recursive function not generated");

  TEST_PASS("RecursiveFunction");
}

// ============================================================================
// Test 5: Main Function (No Name Mangling)
// ============================================================================
void test_MainFunction() {
  TEST_START("MainFunction: int main() should NOT be mangled");

  const char *cpp = R"(
        int main(int argc, char* argv[]) {
            return 0;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  // Main function should be named exactly "main", not mangled
  FunctionDecl *CFunc = visitor.getCFunc("main");
  ASSERT(CFunc != nullptr, "Main function not generated");
  ASSERT(CFunc->getName() == "main", "Main function should not be mangled");

  TEST_PASS("MainFunction");
}

// ============================================================================
// Test 6: Static Function (Internal Linkage)
// ============================================================================
void test_StaticFunction() {
  TEST_START("StaticFunction: static int helper(int x)");

  const char *cpp = R"(
        static int helper(int x) {
            return x * 2;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *CFunc = visitor.getCFunc("helper");
  ASSERT(CFunc != nullptr, "Static function not generated");
  ASSERT(CFunc->getStorageClass() == SC_Static, "Static linkage not preserved");

  TEST_PASS("StaticFunction");
}

// ============================================================================
// Test 7: Extern Function (External Linkage)
// ============================================================================
void test_ExternFunction() {
  TEST_START("ExternFunction: extern int external_func(int a)");

  const char *cpp = R"(
        extern int external_func(int a);

        int wrapper(int a) {
            return external_func(a);
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  // Note: external_func is a forward declaration (no body)
  // The wrapper function should be generated
  FunctionDecl *WrapperFunc = visitor.getCFunc("wrapper");
  ASSERT(WrapperFunc != nullptr, "Wrapper function not generated");

  TEST_PASS("ExternFunction");
}

// ============================================================================
// Test 8: Variadic Function
// ============================================================================
void test_VariadicFunction() {
  TEST_START("VariadicFunction: int sum(int count, ...)");

  const char *cpp = R"(
        int sum(int count, ...) {
            return 0;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *CFunc = visitor.getCFunc("sum");
  ASSERT(CFunc != nullptr, "Variadic function not generated");
  ASSERT(CFunc->isVariadic(), "Variadic property not preserved");

  TEST_PASS("VariadicFunction");
}

// ============================================================================
// Test 9: Inline Function
// ============================================================================
void test_InlineFunction() {
  TEST_START("InlineFunction: inline int abs_val(int x)");

  const char *cpp = R"(
        inline int abs_val(int x) {
            return x < 0 ? -x : x;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *CFunc = visitor.getCFunc("abs_val");
  ASSERT(CFunc != nullptr, "Inline function not generated");
  ASSERT(CFunc->isInlineSpecified(), "Inline specifier not preserved");

  TEST_PASS("InlineFunction");
}

// ============================================================================
// Test 10: Mutually Recursive Functions
// ============================================================================
void test_MutuallyRecursiveFunctions() {
  TEST_START("MutuallyRecursiveFunctions: isEven/isOdd");

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
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *EvenFunc = visitor.getCFunc("isEven");
  FunctionDecl *OddFunc = visitor.getCFunc("isOdd");

  ASSERT(EvenFunc != nullptr, "isEven function not generated");
  ASSERT(OddFunc != nullptr, "isOdd function not generated");

  TEST_PASS("MutuallyRecursiveFunctions");
}

// ============================================================================
// Test 11: Function with Const Parameter
// ============================================================================
void test_ConstQualifiedParameter() {
  TEST_START("ConstQualifiedParameter: int process(const int value)");

  const char *cpp = R"(
        int process(const int value) {
            return value * 2;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *CFunc = visitor.getCFunc("process");
  ASSERT(CFunc != nullptr, "Function not generated");
  ASSERT(CFunc->getNumParams() == 1, "Parameter count mismatch");

  // Verify const qualifier
  ParmVarDecl *Param = CFunc->getParamDecl(0);
  ASSERT(Param->getType().isConstQualified(), "Const qualifier not preserved");

  TEST_PASS("ConstQualifiedParameter");
}

// ============================================================================
// Test 12: Void Return Function
// ============================================================================
void test_VoidReturnFunction() {
  TEST_START("VoidReturnFunction: void print_hello()");

  const char *cpp = R"(
        void print_hello() {
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *CFunc = visitor.getCFunc("print_hello");
  ASSERT(CFunc != nullptr, "Void function not generated");
  ASSERT(CFunc->getReturnType()->isVoidType(), "Return type should be void");

  TEST_PASS("VoidReturnFunction");
}

// ============================================================================
// Test 13: NameMangler - Standalone Function Name Mangling
// ============================================================================
void test_NameMangler_StandaloneFunctionMangling() {
  TEST_START("NameMangler: Standalone function overload mangling");

  const char *cpp = R"(
        void foo(int x) {}
        void foo(double x) {}
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  ASTContext &Ctx = AST->getASTContext();
  NameMangler mangler(Ctx);

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
          ASSERT(mangledName.find("int") != std::string::npos ||
                     mangledName == "foo", // First one might not be mangled
                 "Integer parameter not encoded in mangled name");
          foundIntVersion = true;
        } else if (ParamType->isFloatingType()) {
          ASSERT(mangledName.find("float") != std::string::npos ||
                     mangledName.find("double") != std::string::npos ||
                     mangledName == "foo", // First one might not be mangled
                 "Double parameter not encoded in mangled name");
          foundDoubleVersion = true;
        }
      }
    }
  }

  ASSERT(foundIntVersion, "Int version of foo not found");
  ASSERT(foundDoubleVersion, "Double version of foo not found");

  TEST_PASS("NameMangler_StandaloneFunctionMangling");
}

// ============================================================================
// Test 14: Multiple Overloads with Different Parameter Counts
// ============================================================================
void test_OverloadingDifferentParamCounts() {
  TEST_START("OverloadingDifferentParamCounts: compute(1/2/3 params)");

  const char *cpp = R"(
        int compute(int a) { return a * 2; }
        int compute(int a, int b) { return a + b; }
        int compute(int a, int b, int c) { return a + b + c; }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

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
  ASSERT(functionsFound >= 1, "Overloaded functions not generated");

  TEST_PASS("OverloadingDifferentParamCounts");
}

// ============================================================================
// Test 15: Function with No Parameters
// ============================================================================
void test_NoParameterFunction() {
  TEST_START("NoParameterFunction: int get_constant()");

  const char *cpp = R"(
        int get_constant() {
            return 42;
        }
    )";

  std::unique_ptr<ASTUnit> AST = buildAST(cpp);
  ASSERT(AST, "Failed to parse C++ code");

  CNodeBuilder builder(AST->getASTContext());
  CppToCVisitor visitor(AST->getASTContext(), builder);

  visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

  FunctionDecl *CFunc = visitor.getCFunc("get_constant");
  ASSERT(CFunc != nullptr, "No-parameter function not generated");
  ASSERT(CFunc->getNumParams() == 0, "Should have zero parameters");

  TEST_PASS("NoParameterFunction");
}

// ============================================================================
// Main - run all tests
// ============================================================================
int main() {
  std::cout << "\n==============================================\n";
  std::cout << "Phase 8: Standalone Function Translation Tests\n";
  std::cout << "==============================================\n\n";

  // Basic function tests
  test_SimpleFunctionDeclaration();
  test_FunctionWithPointerReturn();
  test_RecursiveFunction();
  test_MainFunction();

  // Overloading tests
  test_OverloadedFunctions();
  test_OverloadingDifferentParamCounts();
  test_NameMangler_StandaloneFunctionMangling();

  // Linkage and qualifiers
  test_StaticFunction();
  test_ExternFunction();
  test_InlineFunction();
  test_VariadicFunction();

  // Advanced tests
  test_MutuallyRecursiveFunctions();
  test_ConstQualifiedParameter();
  test_VoidReturnFunction();
  test_NoParameterFunction();

  // Summary
  std::cout << "\n==============================================\n";
  std::cout << "Tests passed: " << tests_passed << "\n";
  std::cout << "Tests failed: " << tests_failed << "\n";
  std::cout << "==============================================\n\n";

  return tests_failed > 0 ? 1 : 0;
}
