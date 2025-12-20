// TDD Tests for ACSLFunctionAnnotator - Epic #193, Story #196
// Comprehensive ACSL function contract generation

#include "ACSLFunctionAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <string>
#include <memory>

using namespace clang;

// Simple test framework
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }
#define ASSERT_CONTAINS(haystack, needle, msg) \
    if ((haystack).find(needle) == std::string::npos) { \
        TEST_FAIL("", std::string(msg) + " - Expected to find: " + needle); \
        return; \
    }

// Helper: Parse C++ code and return FunctionDecl
FunctionDecl* parseFunctionDecl(const std::string& code, const std::string& funcName) {
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
    if (!AST) return nullptr;

    ASTContext& ctx = AST->getASTContext();
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();

    for (auto* decl : TU->decls()) {
        if (auto* func = dyn_cast<FunctionDecl>(decl)) {
            if (func->getNameAsString() == funcName) {
                return func;
            }
        }
    }
    return nullptr;
}

// Test 1: Simple function with no parameters - assigns \nothing
void test_SimplePureFunction() {
    TEST_START("SimplePureFunction");

    std::string code = "int getValue() { return 42; }";
    FunctionDecl* func = parseFunctionDecl(code, "getValue");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "assigns \\nothing", "Pure function should have assigns \\nothing");
    ASSERT_CONTAINS(contract, "/*@", "Contract should be ACSL comment");
    ASSERT_CONTAINS(contract, "*/", "Contract should have closing comment");

    TEST_PASS("SimplePureFunction");
}

// Test 2: Function with pointer parameter - requires \valid
void test_PointerParameterValidity() {
    TEST_START("PointerParameterValidity");

    std::string code = "void reset(int* ptr) { *ptr = 0; }";
    FunctionDecl* func = parseFunctionDecl(code, "reset");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "requires \\valid(ptr)", "Pointer param should have \\valid clause");
    ASSERT_CONTAINS(contract, "assigns *ptr", "Pointer deref should be in assigns");

    TEST_PASS("PointerParameterValidity");
}

// Test 3: Function with const pointer - requires \valid_read
void test_ConstPointerReadOnly() {
    TEST_START("ConstPointerReadOnly");

    std::string code = "int getValue(const int* ptr) { return *ptr; }";
    FunctionDecl* func = parseFunctionDecl(code, "getValue");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\valid_read(ptr)", "Const pointer should have \\valid_read");
    ASSERT_CONTAINS(contract, "assigns \\nothing", "Read-only function should have assigns \\nothing");

    TEST_PASS("ConstPointerReadOnly");
}

// Test 4: Array function with size parameter - requires array bounds
void test_ArrayBoundsAnnotation() {
    TEST_START("ArrayBoundsAnnotation");

    std::string code = "void fillArray(int* arr, unsigned int n) { for (unsigned int i = 0; i < n; i++) arr[i] = 0; }";
    FunctionDecl* func = parseFunctionDecl(code, "fillArray");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\valid(arr + (0..n-1))", "Array should have bounds annotation");
    ASSERT_CONTAINS(contract, "assigns arr[0..n-1]", "Array assigns should include range");

    TEST_PASS("ArrayBoundsAnnotation");
}

// Test 5: Function with quantified postcondition - \forall
void test_QuantifiedPostcondition() {
    TEST_START("QuantifiedPostcondition");

    std::string code = "void fillArray(int* arr, unsigned int n, int value) { for (unsigned int i = 0; i < n; i++) arr[i] = value; }";
    FunctionDecl* func = parseFunctionDecl(code, "fillArray");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\forall integer", "Should generate forall quantifier");
    ASSERT_CONTAINS(contract, "arr[", "Quantifier should reference array");
    ASSERT_CONTAINS(contract, "== value", "Postcondition should relate to value parameter");

    TEST_PASS("QuantifiedPostcondition");
}

// Test 6: Function modifying state - \old() postcondition
void test_OldValuePostcondition() {
    TEST_START("OldValuePostcondition");

    std::string code = "void increment(int* counter) { (*counter)++; }";
    FunctionDecl* func = parseFunctionDecl(code, "increment");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\old(*counter)", "Should use \\old for previous value");
    ASSERT_CONTAINS(contract, "assigns *counter", "Should assign counter");

    TEST_PASS("OldValuePostcondition");
}

// Test 7: Function returning pointer - \valid(\result) or null
void test_PointerReturnValue() {
    TEST_START("PointerReturnValue");

    std::string code = "int* allocate(unsigned int n) { return new int[n]; }";
    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\result", "Return value should be referenced");
    ASSERT_CONTAINS(contract, "\\valid(\\result)", "Pointer return should check validity");

    TEST_PASS("PointerReturnValue");
}

// Test 8: Function with separation constraint
void test_SeparationConstraint() {
    TEST_START("SeparationConstraint");

    std::string code = "void swap(int* a, int* b) { int temp = *a; *a = *b; *b = temp; }";
    FunctionDecl* func = parseFunctionDecl(code, "swap");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\valid(a)", "First pointer should have \\valid");
    ASSERT_CONTAINS(contract, "\\valid(b)", "Second pointer should have \\valid");
    ASSERT_CONTAINS(contract, "\\separated(a, b)", "Pointers should be separated");
    ASSERT_CONTAINS(contract, "assigns *a, *b", "Both pointers should be in assigns");

    TEST_PASS("SeparationConstraint");
}

// Test 9: Function with unsigned parameter - value constraint
void test_UnsignedParameterConstraint() {
    TEST_START("UnsignedParameterConstraint");

    std::string code = "int compute(unsigned int x) { return x * 2; }";
    FunctionDecl* func = parseFunctionDecl(code, "compute");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    // Unsigned types implicitly >= 0, but we document it explicitly
    ASSERT_CONTAINS(contract, "x >= 0", "Unsigned parameter should have >= 0 constraint");

    TEST_PASS("UnsignedParameterConstraint");
}

// Test 10: Function with size parameter - n >= 0 constraint
void test_SizeParameterConstraint() {
    TEST_START("SizeParameterConstraint");

    std::string code = "void process(int* arr, unsigned int size) { }";
    FunctionDecl* func = parseFunctionDecl(code, "process");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "size >= 0", "Size parameter should have >= 0 constraint");

    TEST_PASS("SizeParameterConstraint");
}

// Test 11: Search function with existential quantifier
void test_ExistentialQuantifier() {
    TEST_START("ExistentialQuantifier");

    std::string code = "int findMax(const int* arr, unsigned int n) { int max = arr[0]; for (unsigned int i = 1; i < n; i++) if (arr[i] > max) max = arr[i]; return max; }";
    FunctionDecl* func = parseFunctionDecl(code, "findMax");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\exists integer", "Should generate exists quantifier");
    ASSERT_CONTAINS(contract, "\\result == arr[", "Postcondition should relate result to array element");

    TEST_PASS("ExistentialQuantifier");
}

// Test 12: Function with multiple pointer parameters - comprehensive assigns
void test_MultiplePointerAssigns() {
    TEST_START("MultiplePointerAssigns");

    std::string code = "void copyArray(int* dst, const int* src, unsigned int n) { for (unsigned int i = 0; i < n; i++) dst[i] = src[i]; }";
    FunctionDecl* func = parseFunctionDecl(code, "copyArray");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\valid(dst + (0..n-1))", "Destination array bounds");
    ASSERT_CONTAINS(contract, "\\valid_read(src + (0..n-1))", "Source array bounds (read-only)");
    ASSERT_CONTAINS(contract, "assigns dst[0..n-1]", "Assigns should include dst range");
    ASSERT_CONTAINS(contract, "\\forall integer", "Should have quantified postcondition");

    TEST_PASS("MultiplePointerAssigns");
}

// Test 13: Void function with no side effects
void test_VoidFunctionNoSideEffects() {
    TEST_START("VoidFunctionNoSideEffects");

    std::string code = "void doNothing() { }";
    FunctionDecl* func = parseFunctionDecl(code, "doNothing");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "assigns \\nothing", "Void function with no params should have assigns \\nothing");

    TEST_PASS("VoidFunctionNoSideEffects");
}

// Test 14: Function with fresh memory allocation
void test_FreshMemoryAllocation() {
    TEST_START("FreshMemoryAllocation");

    std::string code = "int* allocate(unsigned int n) { int* ptr = new int[n]; return ptr; }";
    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLFunctionAnnotator annotator;
    std::string contract = annotator.generateFunctionContract(func);

    ASSERT_CONTAINS(contract, "\\fresh(\\result", "Allocation should use \\fresh");

    TEST_PASS("FreshMemoryAllocation");
}

// Test 15: Integration test - verify ACSL level configuration
void test_ACSLLevelConfiguration() {
    TEST_START("ACSLLevelConfiguration");

    std::string code = "int add(int a, int b) { return a + b; }";
    FunctionDecl* func = parseFunctionDecl(code, "add");
    ASSERT(func != nullptr, "Failed to parse function");

    // Test with Basic level (should generate less)
    ACSLFunctionAnnotator annotatorBasic(ACSLLevel::Basic);
    std::string contractBasic = annotatorBasic.generateFunctionContract(func);

    // Test with Full level (should generate more)
    ACSLFunctionAnnotator annotatorFull(ACSLLevel::Full);
    std::string contractFull = annotatorFull.generateFunctionContract(func);

    // Full level should have more detail
    ASSERT(contractFull.length() >= contractBasic.length(),
           "Full ACSL level should generate equal or more annotations than Basic");

    TEST_PASS("ACSLLevelConfiguration");
}

int main() {
    std::cout << "=== ACSLFunctionAnnotator Tests (Story #196) ===" << std::endl << std::endl;

    // Run all tests
    test_SimplePureFunction();
    test_PointerParameterValidity();
    test_ConstPointerReadOnly();
    test_ArrayBoundsAnnotation();
    test_QuantifiedPostcondition();
    test_OldValuePostcondition();
    test_PointerReturnValue();
    test_SeparationConstraint();
    test_UnsignedParameterConstraint();
    test_SizeParameterConstraint();
    test_ExistentialQuantifier();
    test_MultiplePointerAssigns();
    test_VoidFunctionNoSideEffects();
    test_FreshMemoryAllocation();
    test_ACSLLevelConfiguration();

    // Print summary
    std::cout << std::endl << "=== Test Summary ===" << std::endl;
    std::cout << "Passed: " << tests_passed << std::endl;
    std::cout << "Failed: " << tests_failed << std::endl;

    return tests_failed > 0 ? 1 : 0;
}
