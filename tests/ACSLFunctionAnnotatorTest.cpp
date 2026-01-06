// TDD Tests for ACSLFunctionAnnotator - Epic #193, Story #196
// Comprehensive ACSL function contract generation

#include <gtest/gtest.h>
#include "ACSLFunctionAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <string>
#include <memory>
#include <vector>

using namespace clang;

// Global storage for AST units to keep them alive
static std::vector<std::unique_ptr<ASTUnit>> persistentASTs;

// Helper: Parse C++ code and return FunctionDecl
FunctionDecl* parseFunctionDecl(const std::string& code, const std::string& funcName) {
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
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

// Test 1: Simple function with no parameters - assigns \nothing

// Test fixture
class ACSLFunctionAnnotatorTest : public ::testing::Test {
protected:
};

TEST_F(ACSLFunctionAnnotatorTest, SimplePureFunction) {
    std::string code = "int getValue() { return 42; }";
        FunctionDecl* func = parseFunctionDecl(code, "getValue");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("assigns \\nothing"), std::string::npos) << "Pure function should have assigns \\nothing";
        EXPECT_NE((contract).find("/*@"), std::string::npos) << "Contract should be ACSL comment";
        EXPECT_NE((contract).find("*/"), std::string::npos) << "Contract should have closing comment";
}

TEST_F(ACSLFunctionAnnotatorTest, PointerParameterValidity) {
    std::string code = "void reset(int* ptr) { *ptr = 0; }";
        FunctionDecl* func = parseFunctionDecl(code, "reset");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("requires \\valid(ptr)"), std::string::npos) << "Pointer param should have \\valid clause";
        EXPECT_NE((contract).find("assigns *ptr"), std::string::npos) << "Pointer deref should be in assigns";
}

TEST_F(ACSLFunctionAnnotatorTest, ConstPointerReadOnly) {
    std::string code = "int getValue(const int* ptr) { return *ptr; }";
        FunctionDecl* func = parseFunctionDecl(code, "getValue");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\valid_read(ptr)"), std::string::npos) << "Const pointer should have \\valid_read";
        EXPECT_NE((contract).find("assigns \\nothing"), std::string::npos) << "Read-only function should have assigns \\nothing";
}

TEST_F(ACSLFunctionAnnotatorTest, ArrayBoundsAnnotation) {
    std::string code = "void fillArray(int* arr, unsigned int n) { for (unsigned int i = 0; i < n; i++) arr[i] = 0; }";
        FunctionDecl* func = parseFunctionDecl(code, "fillArray");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\valid(arr + (0..n-1))"), std::string::npos) << "Array should have bounds annotation";
        EXPECT_NE((contract).find("assigns arr[0..n-1]"), std::string::npos) << "Array assigns should include range";
}

TEST_F(ACSLFunctionAnnotatorTest, QuantifiedPostcondition) {
    std::string code = "void fillArray(int* arr, unsigned int n, int value) { for (unsigned int i = 0; i < n; i++) arr[i] = value; }";
        FunctionDecl* func = parseFunctionDecl(code, "fillArray");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\forall integer"), std::string::npos) << "Should generate forall quantifier";
        EXPECT_NE((contract).find("arr["), std::string::npos) << "Quantifier should reference array";
        EXPECT_NE((contract).find("== value"), std::string::npos) << "Postcondition should relate to value parameter";
}

TEST_F(ACSLFunctionAnnotatorTest, OldValuePostcondition) {
    std::string code = "void increment(int* counter) { (*counter)++; }";
        FunctionDecl* func = parseFunctionDecl(code, "increment");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\old(*counter)"), std::string::npos) << "Should use \\old for previous value";
        EXPECT_NE((contract).find("assigns *counter"), std::string::npos) << "Should assign counter";
}

TEST_F(ACSLFunctionAnnotatorTest, PointerReturnValue) {
    std::string code = "int* allocate(unsigned int n) { return new int[n]; }";
        FunctionDecl* func = parseFunctionDecl(code, "allocate");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\result"), std::string::npos) << "Return value should be referenced";
        EXPECT_NE((contract).find("\\valid(\\result)"), std::string::npos) << "Pointer return should check validity";
}

TEST_F(ACSLFunctionAnnotatorTest, SeparationConstraint) {
    std::string code = "void swap(int* a, int* b) { int temp = *a; *a = *b; *b = temp; }";
        FunctionDecl* func = parseFunctionDecl(code, "swap");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\valid(a)"), std::string::npos) << "First pointer should have \\valid";
        EXPECT_NE((contract).find("\\valid(b)"), std::string::npos) << "Second pointer should have \\valid";
        EXPECT_NE((contract).find("\\separated(a"), std::string::npos) << "Pointers should be separated";
        EXPECT_NE((contract).find("assigns *a"), std::string::npos) << "Both pointers should be in assigns";
}

TEST_F(ACSLFunctionAnnotatorTest, UnsignedParameterConstraint) {
    std::string code = "int compute(unsigned int x) { return x * 2; }";
        FunctionDecl* func = parseFunctionDecl(code, "compute");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        // Unsigned types implicitly >= 0, but we document it explicitly
        EXPECT_NE((contract).find("x >= 0"), std::string::npos) << "Unsigned parameter should have >= 0 constraint";
}

TEST_F(ACSLFunctionAnnotatorTest, SizeParameterConstraint) {
    std::string code = "void process(int* arr, unsigned int size) { }";
        FunctionDecl* func = parseFunctionDecl(code, "process");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("size >= 0"), std::string::npos) << "Size parameter should have >= 0 constraint";
}

TEST_F(ACSLFunctionAnnotatorTest, ExistentialQuantifier) {
    std::string code = "int findMax(const int* arr, unsigned int n) { int max = arr[0]; for (unsigned int i = 1; i < n; i++) if (arr[i] > max) max = arr[i]; return max; }";
        FunctionDecl* func = parseFunctionDecl(code, "findMax");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\exists integer"), std::string::npos) << "Should generate exists quantifier";
        EXPECT_NE((contract).find("\\result == arr["), std::string::npos) << "Postcondition should relate result to array element";
}

TEST_F(ACSLFunctionAnnotatorTest, MultiplePointerAssigns) {
    std::string code = "void copyArray(int* dst, const int* src, unsigned int n) { for (unsigned int i = 0; i < n; i++) dst[i] = src[i]; }";
        FunctionDecl* func = parseFunctionDecl(code, "copyArray");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\valid(dst + (0..n-1))"), std::string::npos) << "Destination array bounds";
        EXPECT_NE((contract).find("\\valid_read(src + (0..n-1))"), std::string::npos) << "Source array bounds (read-only)";
        EXPECT_NE((contract).find("assigns dst[0..n-1]"), std::string::npos) << "Assigns should include dst range";
        EXPECT_NE((contract).find("\\forall integer"), std::string::npos) << "Should have quantified postcondition";
}

TEST_F(ACSLFunctionAnnotatorTest, VoidFunctionNoSideEffects) {
    std::string code = "void doNothing() { }";
        FunctionDecl* func = parseFunctionDecl(code, "doNothing");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("assigns \\nothing"), std::string::npos) << "Void function with no params should have assigns \\nothing";
}

TEST_F(ACSLFunctionAnnotatorTest, FreshMemoryAllocation) {
    std::string code = "int* allocate(unsigned int n) { int* ptr = new int[n]; return ptr; }";
        FunctionDecl* func = parseFunctionDecl(code, "allocate");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLFunctionAnnotator annotator;
        std::string contract = annotator.generateFunctionContract(func);

        EXPECT_NE((contract).find("\\fresh(\\result"), std::string::npos) << "Allocation should use \\fresh";
}

TEST_F(ACSLFunctionAnnotatorTest, ACSLLevelConfiguration) {
    std::string code = "int add(int a, int b) { return a + b; }";
        FunctionDecl* func = parseFunctionDecl(code, "add");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        // Test with Basic level (should generate less)
        ACSLFunctionAnnotator annotatorBasic(ACSLLevel::Basic);
        std::string contractBasic = annotatorBasic.generateFunctionContract(func);

        // Test with Full level (should generate more)
        ACSLFunctionAnnotator annotatorFull(ACSLLevel::Full);
        std::string contractFull = annotatorFull.generateFunctionContract(func);

        // Full level should have more detail
        ASSERT_TRUE(contractFull.length() >= contractBasic.length()) << "Full ACSL level should generate equal or more annotations than Basic";
}
