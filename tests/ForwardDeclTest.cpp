// TDD Tests for Forward Declaration Support - Epic #19 Implementation
// Story #139: Forward Declaration Support

#include <gtest/gtest.h>
#include "HeaderSeparator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/Decl.h"
#include <set>

using namespace clang;

TEST(ForwardDecl, PointerToStructNeedsForwardDecl) {
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
        ASSERT_TRUE(forwardDecls.size() == 1) << "Expected 1 forward declaration for self-referencing struct";
        ASSERT_TRUE(forwardDecls.count("Node") == 1) << "Expected forward declaration for 'Node'";
}

TEST(ForwardDecl, CircularDependency) {
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
        ASSERT_TRUE(forwardDecls.count("A") == 1) << "Expected forward declaration for 'A'";
        ASSERT_TRUE(forwardDecls.count("B") == 1) << "Expected forward declaration for 'B'";
}

TEST(ForwardDecl, MultiplePointersToSameType) {
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
        ASSERT_TRUE(forwardDecls.size() == 1) << "Expected exactly 1 forward declaration";
        ASSERT_TRUE(forwardDecls.count("Node") == 1) << "Expected forward declaration for 'Node'";
}

TEST(ForwardDecl, NonPointerFieldNoForwardDecl) {
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
        ASSERT_TRUE(forwardDecls.size() == 0) << "Expected 0 forward declarations for non-pointer fields";
}

TEST(ForwardDecl, PointerToPrimitiveNoForwardDecl) {
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
        ASSERT_TRUE(forwardDecls.size() == 0) << "Expected 0 forward declarations for primitive type pointers";
}

TEST(ForwardDecl, ComplexCrossReferences) {
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
        ASSERT_TRUE(forwardDecls.count("Node") == 1) << "Expected forward declaration for 'Node'";
        ASSERT_TRUE(forwardDecls.count("Tree") == 1) << "Expected forward declaration for 'Tree'";
        // Note: Forest doesn't need forward decl because nothing points to it
}
