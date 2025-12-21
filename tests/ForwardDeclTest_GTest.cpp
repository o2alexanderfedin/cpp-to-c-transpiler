// tests/ForwardDeclTest_GTest.cpp
// Migrated from ForwardDeclTest.cpp to Google Test framework
// Story #139: Forward Declaration Support

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/AST/Decl.h"
#include "../include/HeaderSeparator.h"
#include <set>

using namespace clang;

// Test fixture for Forward Declaration tests
class ForwardDeclTestFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return clang::tooling::buildASTFromCode(code);
    }
};

// Test 1: Struct with pointer to another struct → forward decl needed
TEST_F(ForwardDeclTestFixture, PointerToStructNeedsForwardDecl) {
    const char *Code = R"(
        struct Node {
            int data;
            struct Node *next;  // Pointer to incomplete type
        };
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Get forward declarations
    auto forwardDecls = separator.getForwardDecls();

    // Should detect that Node needs a forward declaration (self-reference)
    ASSERT_EQ(forwardDecls.size(), 1)
           << "Expected 1 forward declaration for self-referencing struct";
    ASSERT_EQ(forwardDecls.count("Node"), 1)
           << "Expected forward declaration for 'Node'";
}

// Test 2: Circular dependency - both structs need forward declarations
TEST_F(ForwardDeclTestFixture, CircularDependency) {
    const char *Code = R"(
        struct B;  // Forward declaration already in source (but we detect it anyway)

        struct A {
            struct B *bPtr;
        };

        struct B {
            struct A *aPtr;
        };
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // Both A and B reference each other, so both need forward declarations
    ASSERT_EQ(forwardDecls.count("A"), 1)
           << "Expected forward declaration for 'A'";
    ASSERT_EQ(forwardDecls.count("B"), 1)
           << "Expected forward declaration for 'B'";
}

// Test 3: Multiple pointers to same type → single forward decl
TEST_F(ForwardDeclTestFixture, MultiplePointersToSameType) {
    const char *Code = R"(
        struct Node {
            int data;
            struct Node *next;
            struct Node *prev;
            struct Node *parent;
        };
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // Only one forward decl for Node (set eliminates duplicates)
    ASSERT_EQ(forwardDecls.size(), 1)
           << "Expected exactly 1 forward declaration";
    ASSERT_EQ(forwardDecls.count("Node"), 1)
           << "Expected forward declaration for 'Node'";
}

// Test 4: Non-pointer field → no forward decl
TEST_F(ForwardDeclTestFixture, NonPointerFieldNoForwardDecl) {
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

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // No forward declarations needed (embedded structs, not pointers)
    ASSERT_EQ(forwardDecls.size(), 0)
           << "Expected 0 forward declarations for non-pointer fields";
}

// Test 5: Pointer to primitive type → no forward decl
TEST_F(ForwardDeclTestFixture, PointerToPrimitiveNoForwardDecl) {
    const char *Code = R"(
        struct Container {
            int *intPtr;
            double *doublePtr;
            char *charPtr;
        };
    )";

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // No forward declarations for primitive pointers
    ASSERT_EQ(forwardDecls.size(), 0)
           << "Expected 0 forward declarations for primitive type pointers";
}

// Test 6: Complex case - 3 structs with cross-references
TEST_F(ForwardDeclTestFixture, ComplexCrossReferences) {
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

    auto AST = buildAST(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    auto forwardDecls = separator.getForwardDecls();

    // Tree references Node
    // Node references Tree and Node (self)
    // Forest references Tree
    ASSERT_EQ(forwardDecls.count("Node"), 1)
           << "Expected forward declaration for 'Node'";
    ASSERT_EQ(forwardDecls.count("Tree"), 1)
           << "Expected forward declaration for 'Tree'";
    // Note: Forest doesn't need forward decl because nothing points to it
}
