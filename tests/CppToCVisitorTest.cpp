// TDD Tests for CppToCVisitor - Epic #3 Implementation
// Story #15: Class-to-struct conversion

#include "CppToCVisitor.h"
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

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// ============================================================================
// Story #15: Class-to-Struct Conversion Tests
// ============================================================================

void test_EmptyClass(ASTContext &Ctx) {
    TEST_START("EmptyClass: class Empty {} -> struct Empty {}");

    const char *cpp = "class Empty {};";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    // Run visitor on AST
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify C struct generated
    RecordDecl *CStruct = visitor.getCStruct("Empty");
    ASSERT(CStruct != nullptr, "C struct not generated");
    ASSERT(CStruct->getName() == "Empty", "Struct name mismatch");

    TEST_PASS("EmptyClass");
}

void test_ClassWithFields(ASTContext &Ctx) {
    TEST_START("ClassWithFields: class Point { int x, y; }");

    const char *cpp = "class Point { int x, y; };";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    RecordDecl *CStruct = visitor.getCStruct("Point");
    ASSERT(CStruct != nullptr, "C struct not generated");

    // Count fields
    int fieldCount = 0;
    for (auto *Field : CStruct->fields()) {
        fieldCount++;
    }
    ASSERT(fieldCount == 2, "Expected 2 fields, got different count");

    TEST_PASS("ClassWithFields");
}

void test_MixedAccessSpecifiers(ASTContext &Ctx) {
    TEST_START("MixedAccessSpecifiers: public/private -> all public in C");

    const char *cpp = R"(
        class Point {
        private:
            int x;
        public:
            int y;
        protected:
            int z;
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    RecordDecl *CStruct = visitor.getCStruct("Point");
    ASSERT(CStruct != nullptr, "C struct not generated");

    // All fields should be present (access specifiers ignored in C)
    int fieldCount = 0;
    for (auto *Field : CStruct->fields()) {
        fieldCount++;
    }
    ASSERT(fieldCount == 3, "Expected 3 fields (all access levels)");

    TEST_PASS("MixedAccessSpecifiers");
}

void test_ForwardDeclaration(ASTContext &Ctx) {
    TEST_START("ForwardDeclaration: class Forward; -> skip");

    const char *cpp = "class Forward;";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Forward declarations should be skipped
    RecordDecl *CStruct = visitor.getCStruct("Forward");
    ASSERT(CStruct == nullptr, "Forward declaration should be skipped");

    TEST_PASS("ForwardDeclaration");
}

int main(int argc, const char **argv) {
    // Create a simple test AST for context
    std::unique_ptr<ASTUnit> AST = buildAST("int main() { return 0; }");
    if (!AST) {
        std::cerr << "Failed to create test AST" << std::endl;
        return 1;
    }

    ASTContext &Ctx = AST->getASTContext();

    std::cout << "=== Story #15: Class-to-Struct Conversion Tests ===" << std::endl;

    test_EmptyClass(Ctx);
    test_ClassWithFields(Ctx);
    test_MixedAccessSpecifiers(Ctx);
    test_ForwardDeclaration(Ctx);

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
