// TDD Tests for Forward Declaration Support - Epic #19 Implementation
// Story #139: Forward Declaration Support

#include "HeaderSeparator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/Decl.h"
#include <iostream>
#include <set>

using namespace clang;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Test 1: Struct with pointer to another struct → forward decl needed
void test_PointerToStructNeedsForwardDecl() {
    TEST_START("PointerToStructNeedsForwardDecl");

    const char *Code = R"(
        struct Node {
            int data;
            struct Node *next;  // Pointer to incomplete type
        };
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Get forward declarations
    auto forwardDecls = separator.getForwardDecls();

    // Should detect that Node needs a forward declaration (self-reference)
    ASSERT(forwardDecls.size() == 1,
           "Expected 1 forward declaration for self-referencing struct");
    ASSERT(forwardDecls.count("Node") == 1,
           "Expected forward declaration for 'Node'");

    TEST_PASS("PointerToStructNeedsForwardDecl");
}

// Test 2: Circular dependency - both structs need forward declarations
void test_CircularDependency() {
    TEST_START("CircularDependency");

    const char *Code = R"(
        struct B;  // Forward declaration already in source (but we detect it anyway)

        struct A {
            struct B *bPtr;
        };

        struct B {
            struct A *aPtr;
        };
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // Both A and B reference each other, so both need forward declarations
    ASSERT(forwardDecls.count("A") == 1,
           "Expected forward declaration for 'A'");
    ASSERT(forwardDecls.count("B") == 1,
           "Expected forward declaration for 'B'");

    TEST_PASS("CircularDependency");
}

// Test 3: Multiple pointers to same type → single forward decl
void test_MultiplePointersToSameType() {
    TEST_START("MultiplePointersToSameType");

    const char *Code = R"(
        struct Node {
            int data;
            struct Node *next;
            struct Node *prev;
            struct Node *parent;
        };
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // Only one forward decl for Node (set eliminates duplicates)
    ASSERT(forwardDecls.size() == 1,
           "Expected exactly 1 forward declaration");
    ASSERT(forwardDecls.count("Node") == 1,
           "Expected forward declaration for 'Node'");

    TEST_PASS("MultiplePointersToSameType");
}

// Test 4: Non-pointer field → no forward decl
void test_NonPointerFieldNoForwardDecl() {
    TEST_START("NonPointerFieldNoForwardDecl");

    const char *Code = R"(
        struct Point {
            int x;
            int y;
        };

        struct Rectangle {
            struct Point topLeft;    // Embedded struct (not pointer)
            struct Point bottomRight;
        };
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // No forward declarations needed (embedded structs, not pointers)
    ASSERT(forwardDecls.size() == 0,
           "Expected 0 forward declarations for non-pointer fields");

    TEST_PASS("NonPointerFieldNoForwardDecl");
}

// Test 5: Pointer to primitive type → no forward decl
void test_PointerToPrimitiveNoForwardDecl() {
    TEST_START("PointerToPrimitiveNoForwardDecl");

    const char *Code = R"(
        struct Container {
            int *intPtr;
            double *doublePtr;
            char *charPtr;
        };
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // No forward declarations for primitive pointers
    ASSERT(forwardDecls.size() == 0,
           "Expected 0 forward declarations for primitive type pointers");

    TEST_PASS("PointerToPrimitiveNoForwardDecl");
}

// Test 6: Complex case - 3 structs with cross-references
void test_ComplexCrossReferences() {
    TEST_START("ComplexCrossReferences");

    const char *Code = R"(
        struct Tree {
            int value;
            struct Node *root;
        };

        struct Node {
            int data;
            struct Tree *owner;
            struct Node *left;
            struct Node *right;
        };

        struct Forest {
            struct Tree *trees;
            int count;
        };
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // Tree references Node
    // Node references Tree and Node (self)
    // Forest references Tree
    ASSERT(forwardDecls.count("Node") == 1,
           "Expected forward declaration for 'Node'");
    ASSERT(forwardDecls.count("Tree") == 1,
           "Expected forward declaration for 'Tree'");
    // Note: Forest doesn't need forward decl because nothing points to it

    TEST_PASS("ComplexCrossReferences");
}

int main() {
    std::cout << "\n=== Forward Declaration Tests (Story #139) ===\n\n";

    // Run all tests
    test_PointerToStructNeedsForwardDecl();
    test_CircularDependency();
    test_MultiplePointersToSameType();
    test_NonPointerFieldNoForwardDecl();
    test_PointerToPrimitiveNoForwardDecl();
    test_ComplexCrossReferences();

    // Summary
    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << tests_passed << "\n";
    std::cout << "Failed: " << tests_failed << "\n";

    return tests_failed > 0 ? 1 : 0;
}
