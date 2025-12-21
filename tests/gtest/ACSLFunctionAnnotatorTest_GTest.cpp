// tests/gtest/ACSLFunctionAnnotatorTest_GTest.cpp
// Unit tests for ACSL Function Annotator (Epic #193, Story #196)
// Migrated to Google Test framework
//
// Comprehensive ACSL function contract generation

#include "../../include/ACSLFunctionAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;
using namespace std;

// Store AST units to prevent premature destruction
// FIX: Heap-use-after-free bug - keeps ASTUnits alive until program exit
static vector<unique_ptr<ASTUnit>> persistentASTs;

// Test fixture for ACSL Function Annotator
class ACSLFunctionAnnotatorTest : public ::testing::Test {
protected:
    ACSLFunctionAnnotator annotator;

    // Helper: Parse C++ code and return FunctionDecl
    FunctionDecl* parseFunctionDecl(const string& code, const string& funcName) {
        unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

        ASTContext& ctx = AST->getASTContext();
        TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();

        FunctionDecl* result = nullptr;
        for (auto* decl : TU->decls()) {
            if (auto* func = dyn_cast<FunctionDecl>(decl)) {
                if (func->getNameAsString() == funcName) {
                    result = func;
                    break;
                }
            }
        }

        // Keep AST alive until program exit to prevent dangling pointers
        persistentASTs.push_back(std::move(AST));
        return result;
    }

    void SetUp() override {
        annotator = ACSLFunctionAnnotator();
    }
};

// Test 1: Simple function with no parameters - assigns \nothing
TEST_F(ACSLFunctionAnnotatorTest, SimplePureFunction) {
    string code = "int getValue() { return 42; }";
    FunctionDecl* func = parseFunctionDecl(code, "getValue");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("assigns \\nothing"), string::npos)
        << "Pure function should have assigns \\nothing";
    EXPECT_NE(contract.find("/*@"), string::npos)
        << "Contract should be ACSL comment";
    EXPECT_NE(contract.find("*/"), string::npos)
        << "Contract should have closing comment";
}

// Test 2: Function with pointer parameter - requires \valid
TEST_F(ACSLFunctionAnnotatorTest, PointerParameterValidity) {
    string code = "void reset(int* ptr) { *ptr = 0; }";
    FunctionDecl* func = parseFunctionDecl(code, "reset");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("requires \\valid(ptr)"), string::npos)
        << "Pointer param should have \\valid clause";
    EXPECT_NE(contract.find("assigns *ptr"), string::npos)
        << "Pointer deref should be in assigns";
}

// Test 3: Function with const pointer - requires \valid_read
TEST_F(ACSLFunctionAnnotatorTest, ConstPointerReadOnly) {
    string code = "int getValue(const int* ptr) { return *ptr; }";
    FunctionDecl* func = parseFunctionDecl(code, "getValue");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\valid_read(ptr)"), string::npos)
        << "Const pointer should have \\valid_read";
    EXPECT_NE(contract.find("assigns \\nothing"), string::npos)
        << "Read-only function should have assigns \\nothing";
}

// Test 4: Array function with size parameter - requires array bounds
TEST_F(ACSLFunctionAnnotatorTest, ArrayBoundsAnnotation) {
    string code = "void fillArray(int* arr, unsigned int n) { for (unsigned int i = 0; i < n; i++) arr[i] = 0; }";
    FunctionDecl* func = parseFunctionDecl(code, "fillArray");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\valid(arr + (0..n-1))"), string::npos)
        << "Array should have bounds annotation";
    EXPECT_NE(contract.find("assigns arr[0..n-1]"), string::npos)
        << "Array assigns should include range";
}

// Test 5: Function with quantified postcondition - \forall
TEST_F(ACSLFunctionAnnotatorTest, QuantifiedPostcondition) {
    string code = "void fillArray(int* arr, unsigned int n, int value) { for (unsigned int i = 0; i < n; i++) arr[i] = value; }";
    FunctionDecl* func = parseFunctionDecl(code, "fillArray");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\forall integer"), string::npos)
        << "Should generate forall quantifier";
    EXPECT_NE(contract.find("arr["), string::npos)
        << "Quantifier should reference array";
    EXPECT_NE(contract.find("== value"), string::npos)
        << "Postcondition should relate to value parameter";
}

// Test 6: Function modifying state - \old() postcondition
TEST_F(ACSLFunctionAnnotatorTest, OldValuePostcondition) {
    string code = "void increment(int* counter) { (*counter)++; }";
    FunctionDecl* func = parseFunctionDecl(code, "increment");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\old(*counter)"), string::npos)
        << "Should use \\old for previous value";
    EXPECT_NE(contract.find("assigns *counter"), string::npos)
        << "Should assign counter";
}

// Test 7: Function returning pointer - \valid(\result) or null
TEST_F(ACSLFunctionAnnotatorTest, PointerReturnValue) {
    string code = "int* allocate(unsigned int n) { return new int[n]; }";
    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\result"), string::npos)
        << "Return value should be referenced";
    EXPECT_NE(contract.find("\\valid(\\result)"), string::npos)
        << "Pointer return should check validity";
}

// Test 8: Function with separation constraint
TEST_F(ACSLFunctionAnnotatorTest, SeparationConstraint) {
    string code = "void swap(int* a, int* b) { int temp = *a; *a = *b; *b = temp; }";
    FunctionDecl* func = parseFunctionDecl(code, "swap");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\valid(a)"), string::npos)
        << "First pointer should have \\valid";
    EXPECT_NE(contract.find("\\valid(b)"), string::npos)
        << "Second pointer should have \\valid";
    EXPECT_NE(contract.find("\\separated(a, b)"), string::npos)
        << "Pointers should be separated";
    EXPECT_NE(contract.find("assigns *a, *b"), string::npos)
        << "Both pointers should be in assigns";
}

// Test 9: Function with unsigned parameter - value constraint
TEST_F(ACSLFunctionAnnotatorTest, UnsignedParameterConstraint) {
    string code = "int compute(unsigned int x) { return x * 2; }";
    FunctionDecl* func = parseFunctionDecl(code, "compute");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    // Unsigned types implicitly >= 0, but we document it explicitly
    EXPECT_NE(contract.find("x >= 0"), string::npos)
        << "Unsigned parameter should have >= 0 constraint";
}

// Test 10: Function with size parameter - n >= 0 constraint
TEST_F(ACSLFunctionAnnotatorTest, SizeParameterConstraint) {
    string code = "void process(int* arr, unsigned int size) { }";
    FunctionDecl* func = parseFunctionDecl(code, "process");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("size >= 0"), string::npos)
        << "Size parameter should have >= 0 constraint";
}

// Test 11: Search function with existential quantifier
TEST_F(ACSLFunctionAnnotatorTest, ExistentialQuantifier) {
    string code = "int findMax(const int* arr, unsigned int n) { int max = arr[0]; for (unsigned int i = 1; i < n; i++) if (arr[i] > max) max = arr[i]; return max; }";
    FunctionDecl* func = parseFunctionDecl(code, "findMax");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\exists integer"), string::npos)
        << "Should generate exists quantifier";
    EXPECT_NE(contract.find("\\result == arr["), string::npos)
        << "Postcondition should relate result to array element";
}

// Test 12: Function with multiple pointer parameters - comprehensive assigns
TEST_F(ACSLFunctionAnnotatorTest, MultiplePointerAssigns) {
    string code = "void copyArray(int* dst, const int* src, unsigned int n) { for (unsigned int i = 0; i < n; i++) dst[i] = src[i]; }";
    FunctionDecl* func = parseFunctionDecl(code, "copyArray");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\valid(dst + (0..n-1))"), string::npos)
        << "Destination array bounds";
    EXPECT_NE(contract.find("\\valid_read(src + (0..n-1))"), string::npos)
        << "Source array bounds (read-only)";
    EXPECT_NE(contract.find("assigns dst[0..n-1]"), string::npos)
        << "Assigns should include dst range";
    EXPECT_NE(contract.find("\\forall integer"), string::npos)
        << "Should have quantified postcondition";
}

// Test 13: Void function with no side effects
TEST_F(ACSLFunctionAnnotatorTest, VoidFunctionNoSideEffects) {
    string code = "void doNothing() { }";
    FunctionDecl* func = parseFunctionDecl(code, "doNothing");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("assigns \\nothing"), string::npos)
        << "Void function with no params should have assigns \\nothing";
}

// Test 14: Function with fresh memory allocation
TEST_F(ACSLFunctionAnnotatorTest, FreshMemoryAllocation) {
    string code = "int* allocate(unsigned int n) { int* ptr = new int[n]; return ptr; }";
    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = annotator.generateFunctionContract(func);

    EXPECT_NE(contract.find("\\fresh(\\result"), string::npos)
        << "Allocation should use \\fresh";
}

// Test 15: Integration test - verify ACSL level configuration
TEST_F(ACSLFunctionAnnotatorTest, ACSLLevelConfiguration) {
    string code = "int add(int a, int b) { return a + b; }";
    FunctionDecl* func = parseFunctionDecl(code, "add");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    // Test with Basic level (should generate less)
    ACSLFunctionAnnotator annotatorBasic(ACSLLevel::Basic);
    string contractBasic = annotatorBasic.generateFunctionContract(func);

    // Test with Full level (should generate more)
    ACSLFunctionAnnotator annotatorFull(ACSLLevel::Full);
    string contractFull = annotatorFull.generateFunctionContract(func);

    // Full level should have more detail
    EXPECT_GE(contractFull.length(), contractBasic.length())
        << "Full ACSL level should generate equal or more annotations than Basic";
}

// Main function for standalone execution
int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
