// Integration tests for mutual struct references with forward declarations
// Tests Phase 28-01 feature: Forward declarations in header files

#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include "TranspilerAPI.h"

using ::testing::HasSubstr;
using ::testing::Not;

class TranspilerAPI_MutualStructReferences : public ::testing::Test {
protected:
    cpptoc::TranspileOptions options;

    void SetUp() override {
        // Use default options for most tests
    }
};

// Test 1: Self-Referencing Struct (Linked List Node)
TEST_F(TranspilerAPI_MutualStructReferences, SelfReferencingStruct) {
    std::string cpp = R"(
        struct Node {
            int data;
            struct Node* next;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // Forward declaration should be emitted
    EXPECT_THAT(result.h, HasSubstr("// Forward declarations"))
        << "Header should have forward declarations section";
    EXPECT_THAT(result.h, HasSubstr("struct Node;"))
        << "Header should have forward declaration for Node";

    // Full struct definition should be present
    EXPECT_THAT(result.h, HasSubstr("struct Node {"))
        << "Header should have complete struct definition";
    EXPECT_THAT(result.h, HasSubstr("int data;"))
        << "Header should have data field";
    // Accept both "struct Node* next" and "struct Node *next" (C style varies)
    EXPECT_TRUE(result.h.find("struct Node* next;") != std::string::npos ||
                result.h.find("struct Node *next;") != std::string::npos)
        << "Header should have next pointer field";
}

// Test 2: Mutually Referencing Structs (A -> B, B -> A)
TEST_F(TranspilerAPI_MutualStructReferences, MutuallyReferencingStructs) {
    std::string cpp = R"(
        struct A {
            int value;
            struct B* b_ptr;
        };

        struct B {
            double data;
            struct A* a_ptr;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // Both forward declarations should be present
    EXPECT_THAT(result.h, HasSubstr("struct A;"))
        << "Header should have forward declaration for A";
    EXPECT_THAT(result.h, HasSubstr("struct B;"))
        << "Header should have forward declaration for B";

    // Both complete definitions should be present
    EXPECT_THAT(result.h, HasSubstr("struct A {"))
        << "Header should have complete struct A definition";
    EXPECT_THAT(result.h, HasSubstr("struct B {"))
        << "Header should have complete struct B definition";

    // Verify pointer fields are correctly emitted (accept both pointer styles)
    EXPECT_TRUE(result.h.find("struct B* b_ptr;") != std::string::npos ||
                result.h.find("struct B *b_ptr;") != std::string::npos)
        << "Struct A should have pointer to B";
    EXPECT_TRUE(result.h.find("struct A* a_ptr;") != std::string::npos ||
                result.h.find("struct A *a_ptr;") != std::string::npos)
        << "Struct B should have pointer to A";
}

// Test 3: Tree Structure (Parent-Child Relationship)
TEST_F(TranspilerAPI_MutualStructReferences, TreeStructure) {
    std::string cpp = R"(
        struct TreeNode {
            int value;
            struct TreeNode* left;
            struct TreeNode* right;
            struct TreeNode* parent;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // Forward declaration
    EXPECT_THAT(result.h, HasSubstr("struct TreeNode;"))
        << "Header should have forward declaration for TreeNode";

    // Complete definition with all three pointer fields (accept both pointer styles)
    EXPECT_THAT(result.h, HasSubstr("struct TreeNode {"))
        << "Header should have complete struct definition";
    EXPECT_TRUE(result.h.find("struct TreeNode* left;") != std::string::npos ||
                result.h.find("struct TreeNode *left;") != std::string::npos)
        << "TreeNode should have left child pointer";
    EXPECT_TRUE(result.h.find("struct TreeNode* right;") != std::string::npos ||
                result.h.find("struct TreeNode *right;") != std::string::npos)
        << "TreeNode should have right child pointer";
    EXPECT_TRUE(result.h.find("struct TreeNode* parent;") != std::string::npos ||
                result.h.find("struct TreeNode *parent;") != std::string::npos)
        << "TreeNode should have parent pointer";
}

// Test 4: Complex Mutual References (A -> B -> C -> A)
TEST_F(TranspilerAPI_MutualStructReferences, CircularReferenceChain) {
    std::string cpp = R"(
        struct A {
            int a_val;
            struct B* b_ptr;
        };

        struct B {
            int b_val;
            struct C* c_ptr;
        };

        struct C {
            int c_val;
            struct A* a_ptr;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // All three forward declarations should be present
    EXPECT_THAT(result.h, HasSubstr("struct A;"))
        << "Header should have forward declaration for A";
    EXPECT_THAT(result.h, HasSubstr("struct B;"))
        << "Header should have forward declaration for B";
    EXPECT_THAT(result.h, HasSubstr("struct C;"))
        << "Header should have forward declaration for C";

    // All complete definitions should be present
    EXPECT_THAT(result.h, HasSubstr("struct A {"))
        << "Header should have complete struct A definition";
    EXPECT_THAT(result.h, HasSubstr("struct B {"))
        << "Header should have complete struct B definition";
    EXPECT_THAT(result.h, HasSubstr("struct C {"))
        << "Header should have complete struct C definition";

    // Verify circular reference chain (accept both pointer styles)
    EXPECT_TRUE(result.h.find("struct B* b_ptr;") != std::string::npos ||
                result.h.find("struct B *b_ptr;") != std::string::npos)
        << "A should reference B";
    EXPECT_TRUE(result.h.find("struct C* c_ptr;") != std::string::npos ||
                result.h.find("struct C *c_ptr;") != std::string::npos)
        << "B should reference C";
    EXPECT_TRUE(result.h.find("struct A* a_ptr;") != std::string::npos ||
                result.h.find("struct A *a_ptr;") != std::string::npos)
        << "C should reference A (completing the cycle)";
}

// Test 5: Mix of Self-Reference and Mutual References
TEST_F(TranspilerAPI_MutualStructReferences, MixedReferences) {
    std::string cpp = R"(
        struct LinkedListNode {
            int data;
            struct LinkedListNode* next;  // Self-reference
        };

        struct Graph {
            int id;
            struct LinkedListNode* adjacency_list;  // Reference to other struct
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // Forward declaration only for self-referencing struct
    EXPECT_THAT(result.h, HasSubstr("struct LinkedListNode;"))
        << "Header should have forward declaration for LinkedListNode (self-referencing)";
    // Graph doesn't need forward declaration (not self-referencing)

    // Both complete definitions
    EXPECT_THAT(result.h, HasSubstr("struct LinkedListNode {"))
        << "Header should have LinkedListNode definition";
    EXPECT_THAT(result.h, HasSubstr("struct Graph {"))
        << "Header should have Graph definition";
}

// Test 6: No Forward Declarations Needed (No Pointer Fields)
TEST_F(TranspilerAPI_MutualStructReferences, NoPointerFields) {
    std::string cpp = R"(
        struct Point {
            int x;
            int y;
        };

        struct Rectangle {
            int width;
            int height;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // No forward declarations needed (no pointers)
    // The forward declarations section might still exist but be empty,
    // or might not exist at all. Either is acceptable.

    // Struct definitions should still be present
    EXPECT_THAT(result.h, HasSubstr("struct Point {"))
        << "Header should have Point definition";
    EXPECT_THAT(result.h, HasSubstr("struct Rectangle {"))
        << "Header should have Rectangle definition";
}

// Test 7: Forward Declaration with Functions Using Structs
TEST_F(TranspilerAPI_MutualStructReferences, ForwardDeclWithFunctions) {
    std::string cpp = R"(
        struct Node {
            int value;
            struct Node* next;
        };

        void append(struct Node* head, int value) {
            struct Node* current = head;
            while (current->next != nullptr) {
                current = current->next;
            }
            // Append logic here...
        }
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // Forward declaration in header
    EXPECT_THAT(result.h, HasSubstr("struct Node;"))
        << "Header should have forward declaration";

    // Struct definition in header
    EXPECT_THAT(result.h, HasSubstr("struct Node {"))
        << "Header should have struct definition";

    // Function declaration in header (accept both pointer styles and with/without param names)
    EXPECT_TRUE(result.h.find("void append") != std::string::npos &&
                (result.h.find("struct Node*") != std::string::npos || result.h.find("struct Node *") != std::string::npos))
        << "Header should have function declaration with struct Node parameter";

    // Function implementation in .c file (accept both pointer styles and with/without param names)
    EXPECT_THAT(result.c, HasSubstr("#include \"test.cpp.h\""))
        << ".c file should include header";
    EXPECT_TRUE(result.c.find("void append") != std::string::npos &&
                (result.c.find("struct Node*") != std::string::npos || result.c.find("struct Node *") != std::string::npos))
        << ".c file should have function implementation with struct Node parameter";
}

// Test 8: Include Guards with Forward Declarations
TEST_F(TranspilerAPI_MutualStructReferences, IncludeGuardsWithForwardDecls) {
    std::string cpp = R"(
        struct Node {
            int data;
            struct Node* next;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // Include guards should wrap everything
    EXPECT_THAT(result.h, HasSubstr("#ifndef TEST_CPP_H"))
        << "Header should have include guard begin";
    EXPECT_THAT(result.h, HasSubstr("#define TEST_CPP_H"))
        << "Header should define include guard";
    EXPECT_THAT(result.h, HasSubstr("#endif // TEST_CPP_H"))
        << "Header should have include guard end";

    // Forward declaration should be within guards
    std::string header = result.h;
    size_t ifndef_pos = header.find("#ifndef");
    size_t endif_pos = header.find("#endif");
    size_t fwd_pos = header.find("struct Node;");

    EXPECT_LT(ifndef_pos, fwd_pos)
        << "Forward declaration should be after #ifndef";
    EXPECT_LT(fwd_pos, endif_pos)
        << "Forward declaration should be before #endif";
}

// Test 9: Pragma Once with Forward Declarations
TEST_F(TranspilerAPI_MutualStructReferences, PragmaOnceWithForwardDecls) {
    cpptoc::TranspileOptions opts;
    opts.usePragmaOnce = true;

    std::string cpp = R"(
        struct Node {
            int data;
            struct Node* next;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // Should use #pragma once
    EXPECT_THAT(result.h, HasSubstr("#pragma once"))
        << "Header should use #pragma once";
    EXPECT_THAT(result.h, Not(HasSubstr("#ifndef")))
        << "Header should not use include guards";

    // Forward declaration should still be present
    EXPECT_THAT(result.h, HasSubstr("struct Node;"))
        << "Header should have forward declaration";
}

// Test 10: Doubly Linked List (Classic Mutual Reference Case)
TEST_F(TranspilerAPI_MutualStructReferences, DoublyLinkedList) {
    std::string cpp = R"(
        struct DLNode {
            int data;
            struct DLNode* prev;
            struct DLNode* next;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";

    // Forward declaration
    EXPECT_THAT(result.h, HasSubstr("struct DLNode;"))
        << "Header should have forward declaration for DLNode";

    // Complete definition with both pointers (accept both pointer styles)
    EXPECT_THAT(result.h, HasSubstr("struct DLNode {"))
        << "Header should have complete struct definition";
    EXPECT_TRUE(result.h.find("struct DLNode* prev;") != std::string::npos ||
                result.h.find("struct DLNode *prev;") != std::string::npos)
        << "DLNode should have prev pointer";
    EXPECT_TRUE(result.h.find("struct DLNode* next;") != std::string::npos ||
                result.h.find("struct DLNode *next;") != std::string::npos)
        << "DLNode should have next pointer";

    // Verify no placeholder text
    EXPECT_THAT(result.h, Not(HasSubstr("TODO")))
        << "Header should have no TODO markers";
    EXPECT_THAT(result.h, Not(HasSubstr("placeholder")))
        << "Header should have no placeholders";
    EXPECT_THAT(result.c, Not(HasSubstr("TODO")))
        << ".c file should have no TODO markers";
    EXPECT_THAT(result.c, Not(HasSubstr("placeholder")))
        << ".c file should have no placeholders";
}
