// TDD GREEN Phase: Tests for CNodeBuilder type helpers
// Story #9: CNodeBuilder structure and type helpers

#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>

using namespace clang;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

void test_constructor(ASTContext &Ctx) {
    TEST_START("Constructor");
    CNodeBuilder builder(Ctx);
    TEST_PASS("Constructor");
}

void test_intType(ASTContext &Ctx) {
    TEST_START("intType()");
    CNodeBuilder builder(Ctx);
    QualType intTy = builder.intType();
    ASSERT(!intTy.isNull(), "intType returned null");
    ASSERT(intTy->isIntegerType(), "intType not an integer type");
    TEST_PASS("intType()");
}

void test_voidType(ASTContext &Ctx) {
    TEST_START("voidType()");
    CNodeBuilder builder(Ctx);
    QualType voidTy = builder.voidType();
    ASSERT(!voidTy.isNull(), "voidType returned null");
    ASSERT(voidTy->isVoidType(), "voidType not a void type");
    TEST_PASS("voidType()");
}

void test_charType(ASTContext &Ctx) {
    TEST_START("charType()");
    CNodeBuilder builder(Ctx);
    QualType charTy = builder.charType();
    ASSERT(!charTy.isNull(), "charType returned null");
    ASSERT(charTy->isCharType(), "charType not a char type");
    TEST_PASS("charType()");
}

void test_ptrType(ASTContext &Ctx) {
    TEST_START("ptrType()");
    CNodeBuilder builder(Ctx);
    QualType intTy = builder.intType();
    QualType ptrTy = builder.ptrType(intTy);
    ASSERT(!ptrTy.isNull(), "ptrType returned null");
    ASSERT(ptrTy->isPointerType(), "ptrType not a pointer type");
    TEST_PASS("ptrType()");
}

void test_structType(ASTContext &Ctx) {
    TEST_START("structType()");
    CNodeBuilder builder(Ctx);
    QualType structTy = builder.structType("Point");
    ASSERT(!structTy.isNull(), "structType returned null");
    ASSERT(structTy->isStructureType(), "structType not a structure type");
    TEST_PASS("structType()");
}

int main(int argc, const char **argv) {
    // Create a simple test AST
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode("int main() { return 0; }");
    if (!AST) {
        std::cerr << "Failed to create test AST" << std::endl;
        return 1;
    }

    ASTContext &Ctx = AST->getASTContext();

    std::cout << "=== CNodeBuilder Type Helper Tests (Story #9) ===" << std::endl;

    test_constructor(Ctx);
    test_intType(Ctx);
    test_voidType(Ctx);
    test_charType(Ctx);
    test_ptrType(Ctx);
    test_structType(Ctx);

    std::cout << "\n========================================" << std::endl;
    std::cout << "Tests passed: " << tests_passed << std::endl;
    std::cout << "Tests failed: " << tests_failed << std::endl;

    if (tests_failed == 0) {
        std::cout << "\n✓ All tests passed!" << std::endl;
        return 0;
    } else {
        std::cout << "\n✗ Some tests failed!" << std::endl;
        return 1;
    }
}
