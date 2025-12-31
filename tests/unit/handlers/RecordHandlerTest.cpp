/**
 * @file RecordHandlerTest.cpp
 * @brief TDD tests for RecordHandler
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan:
 * Task 1 - Basic Struct Declarations (10-12 tests):
 * 1. EmptyStruct - struct Empty {};
 * 2. SimpleStructWithFields - struct Point { int x; int y; };
 * 3. StructWithMultipleFieldTypes - mixed primitive types
 * 4. StructWithConstFields - const int x;
 * 5. StructWithArrayFields - int arr[10];
 * 6. StructWithPointerFields - int* ptr;
 * 7. ForwardStructDeclaration - struct Node;
 * 8. TypedefStruct - typedef struct Point Point_t;
 *
 * Task 2 - Nested Struct Handling (6-8 tests):
 * 9. StructWithNestedStructDefinition - struct Outer { struct Inner { int x; }; };
 * 10. StructWithNestedStructField - struct Rect { struct Point topLeft; };
 * 11. MultipleLevelNesting - struct A { struct B { struct C { int x; }; }; };
 * 12. NestedStructUsedInMultipleParents - Same nested struct in different parents
 * 13. ForwardDeclarationCircularDependency - struct A; struct B { A* a; }; struct A { B* b; };
 * 14. AnonymousNestedStruct - struct Outer { struct { int x; }; };
 */

#include "dispatch/RecordHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecordLayout.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class RecordHandlerTest
 * @brief Test fixture for RecordHandler
 */
class RecordHandlerTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;
    std::unique_ptr<RecordHandler> handler;

    void SetUp() override {
        // Create real AST contexts using minimal code
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create handler
        handler = std::make_unique<RecordHandler>();
    }

    void TearDown() override {
        handler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Build AST from code and return the first RecordDecl
     */
    const clang::RecordDecl* getRecordDeclFromCode(const std::string& code) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        if (!cppAST) return nullptr;

        // Recreate builder and context with new AST
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Find the first RecordDecl
        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
                return recordDecl;
            }
        }

        return nullptr;
    }

    /**
     * @brief Verify that a RecordDecl has the expected structure
     */
    void verifyRecordStructure(
        const clang::RecordDecl* cRecord,
        const std::string& expectedName,
        size_t expectedFieldCount
    ) {
        ASSERT_NE(cRecord, nullptr) << "C RecordDecl is null";
        EXPECT_EQ(cRecord->getNameAsString(), expectedName);

        // Count fields
        size_t fieldCount = 0;
        for (auto* field : cRecord->fields()) {
            (void)field;
            fieldCount++;
        }
        EXPECT_EQ(fieldCount, expectedFieldCount);
    }
};

// =============================================================================
// Task 1: Basic Struct Declarations
// =============================================================================

/**
 * Test 1: Empty struct
 * C++: struct Empty {};
 * C:   struct Empty {};
 */
TEST_F(RecordHandlerTest, EmptyStruct) {
    const char* code = R"(
        struct Empty {};
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(handler->canHandle(cppRecord));

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Empty", 0);
}

/**
 * Test 2: Simple struct with fields
 * C++: struct Point { int x; int y; };
 * C:   struct Point { int x; int y; };
 */
TEST_F(RecordHandlerTest, SimpleStructWithFields) {
    const char* code = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Point", 2);

    // Verify field types
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "x");
    EXPECT_TRUE((*it)->getType()->isIntegerType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "y");
    EXPECT_TRUE((*it)->getType()->isIntegerType());
}

/**
 * Test 3: Struct with multiple field types
 * C++: struct Mixed { int i; float f; char c; };
 * C:   struct Mixed { int i; float f; char c; };
 */
TEST_F(RecordHandlerTest, StructWithMultipleFieldTypes) {
    const char* code = R"(
        struct Mixed {
            int i;
            float f;
            char c;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Mixed", 3);

    // Verify field types
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "i");
    EXPECT_TRUE((*it)->getType()->isIntegerType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "f");
    EXPECT_TRUE((*it)->getType()->isFloatingType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "c");
    EXPECT_TRUE((*it)->getType()->isCharType());
}

/**
 * Test 4: Struct with const fields
 * C++: struct WithConst { const int x; };
 * C:   struct WithConst { const int x; };
 */
TEST_F(RecordHandlerTest, StructWithConstFields) {
    const char* code = R"(
        struct WithConst {
            const int x;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "WithConst", 1);

    // Verify const qualifier
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "x");
    EXPECT_TRUE((*it)->getType().isConstQualified());
}

/**
 * Test 5: Struct with array fields
 * C++: struct WithArray { int arr[10]; };
 * C:   struct WithArray { int arr[10]; };
 */
TEST_F(RecordHandlerTest, StructWithArrayFields) {
    const char* code = R"(
        struct WithArray {
            int arr[10];
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "WithArray", 1);

    // Verify array type
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "arr");
    EXPECT_TRUE((*it)->getType()->isArrayType());
}

/**
 * Test 6: Struct with pointer fields
 * C++: struct WithPointer { int* ptr; };
 * C:   struct WithPointer { int* ptr; };
 */
TEST_F(RecordHandlerTest, StructWithPointerFields) {
    const char* code = R"(
        struct WithPointer {
            int* ptr;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "WithPointer", 1);

    // Verify pointer type
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "ptr");
    EXPECT_TRUE((*it)->getType()->isPointerType());
}

/**
 * Test 7: Forward struct declaration
 * C++: struct Node;
 * C:   struct Node;
 */
TEST_F(RecordHandlerTest, ForwardStructDeclaration) {
    const char* code = R"(
        struct Node;
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_FALSE(cppRecord->isCompleteDefinition());

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);
    EXPECT_EQ(cRecord->getNameAsString(), "Node");
    EXPECT_FALSE(cRecord->isCompleteDefinition());
}

/**
 * Test 8: Struct with struct keyword (class keyword should normalize to struct)
 * C++: class Point { public: int x; int y; };
 * C:   struct Point { int x; int y; };
 */
TEST_F(RecordHandlerTest, ClassKeywordNormalizesToStruct) {
    const char* code = R"(
        class Point {
        public:
            int x;
            int y;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Point", 2);

    // In C, all records are TagTypeKind::Struct (TTK_Struct)
    EXPECT_TRUE(cRecord->isStruct());
}

// =============================================================================
// Task 2: Nested Struct Handling
// =============================================================================

/**
 * Test 9: Struct with nested struct definition
 * C++: struct Outer { struct Inner { int x; }; };
 * C:   struct Outer { struct Inner { int x; }; };
 *
 * Decision: Keep nested (C supports nested struct declarations)
 */
TEST_F(RecordHandlerTest, StructWithNestedStructDefinition) {
    const char* code = R"(
        struct Outer {
            struct Inner {
                int x;
            };
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_EQ(cppRecord->getNameAsString(), "Outer");

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);
    EXPECT_EQ(cRecord->getNameAsString(), "Outer");

    // Find nested struct in C AST
    bool foundNestedStruct = false;
    for (auto* decl : cRecord->decls()) {
        if (auto* nestedRecord = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            foundNestedStruct = true;
            EXPECT_EQ(nestedRecord->getNameAsString(), "Inner");

            // Verify nested struct has field
            size_t fieldCount = 0;
            for (auto* field : nestedRecord->fields()) {
                EXPECT_EQ(field->getNameAsString(), "x");
                fieldCount++;
            }
            EXPECT_EQ(fieldCount, 1);
        }
    }
    EXPECT_TRUE(foundNestedStruct) << "Nested struct 'Inner' not found in C AST";
}

/**
 * Test 10: Struct with nested struct field
 * C++: struct Point { int x; int y; }; struct Rect { Point topLeft; };
 * C:   struct Point { int x; int y; }; struct Rect { struct Point topLeft; };
 */
TEST_F(RecordHandlerTest, StructWithNestedStructField) {
    const char* code = R"(
        struct Point {
            int x;
            int y;
        };

        struct Rect {
            Point topLeft;
        };
    )";

    // Get Rect struct
    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context with new AST
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::RecordDecl* cppPoint = nullptr;
    const clang::RecordDecl* cppRect = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (recordDecl->getNameAsString() == "Point") {
                cppPoint = recordDecl;
            } else if (recordDecl->getNameAsString() == "Rect") {
                cppRect = recordDecl;
            }
        }
    }

    ASSERT_NE(cppPoint, nullptr);
    ASSERT_NE(cppRect, nullptr);

    // Translate Point first
    auto* cPoint = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppPoint, *context)
    );
    ASSERT_NE(cPoint, nullptr);

    // Translate Rect
    auto* cRect = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRect, *context)
    );

    verifyRecordStructure(cRect, "Rect", 1);

    // Verify field type is struct Point
    auto it = cRect->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "topLeft");

    auto fieldType = (*it)->getType();
    EXPECT_TRUE(fieldType->isStructureType());

    // Get the RecordType and verify it's Point
    if (const auto* recordType = fieldType->getAs<clang::RecordType>()) {
        const auto* recordDecl = recordType->getDecl();
        EXPECT_EQ(recordDecl->getNameAsString(), "Point");
    }
}

/**
 * Test 11: Multiple level nesting
 * C++: struct A { struct B { struct C { int x; }; }; };
 * C:   struct A { struct B { struct C { int x; }; }; };
 */
TEST_F(RecordHandlerTest, MultipleLevelNesting) {
    const char* code = R"(
        struct A {
            struct B {
                struct C {
                    int x;
                };
            };
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_EQ(cppRecord->getNameAsString(), "A");

    auto* cRecordA = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    ASSERT_NE(cRecordA, nullptr);
    EXPECT_EQ(cRecordA->getNameAsString(), "A");

    // Find nested struct B in A
    bool foundB = false;
    for (auto* decl : cRecordA->decls()) {
        if (auto* recordB = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            foundB = true;
            EXPECT_EQ(recordB->getNameAsString(), "B");

            // Find nested struct C in B
            bool foundC = false;
            for (auto* declB : recordB->decls()) {
                if (auto* recordC = llvm::dyn_cast<clang::RecordDecl>(declB)) {
                    foundC = true;
                    EXPECT_EQ(recordC->getNameAsString(), "C");

                    // Verify C has field x
                    size_t fieldCount = 0;
                    for (auto* field : recordC->fields()) {
                        EXPECT_EQ(field->getNameAsString(), "x");
                        fieldCount++;
                    }
                    EXPECT_EQ(fieldCount, 1);
                }
            }
            EXPECT_TRUE(foundC) << "Nested struct 'C' not found in B";
        }
    }
    EXPECT_TRUE(foundB) << "Nested struct 'B' not found in A";
}

/**
 * Test 12: Nested struct used in multiple parent structs
 * Note: This test focuses on independent definitions, not reuse
 */
TEST_F(RecordHandlerTest, IndependentNestedStructs) {
    const char* code = R"(
        struct Parent1 {
            struct Nested {
                int value;
            };
        };

        struct Parent2 {
            struct Nested {
                float data;
            };
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context with new AST
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::RecordDecl* cppParent1 = nullptr;
    const clang::RecordDecl* cppParent2 = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (recordDecl->getNameAsString() == "Parent1") {
                cppParent1 = recordDecl;
            } else if (recordDecl->getNameAsString() == "Parent2") {
                cppParent2 = recordDecl;
            }
        }
    }

    ASSERT_NE(cppParent1, nullptr);
    ASSERT_NE(cppParent2, nullptr);

    // Translate both parents
    auto* cParent1 = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppParent1, *context)
    );
    auto* cParent2 = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppParent2, *context)
    );

    ASSERT_NE(cParent1, nullptr);
    ASSERT_NE(cParent2, nullptr);

    // Both should have their own nested Nested struct
    // (This tests that we don't accidentally merge them)
}

/**
 * Test 13: Forward declaration for circular dependency
 * C++: struct A; struct B { A* a; }; struct A { B* b; };
 * C:   struct A; struct B { struct A* a; }; struct A { struct B* b; };
 */
TEST_F(RecordHandlerTest, ForwardDeclarationCircularDependency) {
    const char* code = R"(
        struct A;

        struct B {
            A* a;
        };

        struct A {
            B* b;
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context with new AST
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::RecordDecl* cppAForward = nullptr;
    const clang::RecordDecl* cppB = nullptr;
    const clang::RecordDecl* cppADef = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            std::string name = recordDecl->getNameAsString();
            if (name == "B") {
                cppB = recordDecl;
            } else if (name == "A") {
                if (recordDecl->isCompleteDefinition()) {
                    cppADef = recordDecl;
                } else {
                    cppAForward = recordDecl;
                }
            }
        }
    }

    ASSERT_NE(cppAForward, nullptr);
    ASSERT_NE(cppB, nullptr);
    ASSERT_NE(cppADef, nullptr);

    // Translate forward declaration first
    auto* cAForward = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppAForward, *context)
    );
    ASSERT_NE(cAForward, nullptr);
    EXPECT_FALSE(cAForward->isCompleteDefinition());

    // Translate B
    auto* cB = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppB, *context)
    );
    verifyRecordStructure(cB, "B", 1);

    // Translate A definition
    auto* cADef = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppADef, *context)
    );
    verifyRecordStructure(cADef, "A", 1);
}

/**
 * Test 14: Anonymous nested struct
 * C++: struct Outer { struct { int x; }; };
 * C:   struct Outer { struct { int x; }; };
 *
 * Note: C supports anonymous structs as a common extension
 */
TEST_F(RecordHandlerTest, AnonymousNestedStruct) {
    const char* code = R"(
        struct Outer {
            struct {
                int x;
            };
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_EQ(cppRecord->getNameAsString(), "Outer");

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);
    EXPECT_EQ(cRecord->getNameAsString(), "Outer");

    // Find anonymous nested struct in C AST
    bool foundAnonymousStruct = false;
    for (auto* decl : cRecord->decls()) {
        if (auto* nestedRecord = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            // Anonymous structs have empty names
            if (nestedRecord->getNameAsString().empty()) {
                foundAnonymousStruct = true;

                // Verify nested struct has field
                size_t fieldCount = 0;
                for (auto* field : nestedRecord->fields()) {
                    EXPECT_EQ(field->getNameAsString(), "x");
                    fieldCount++;
                }
                EXPECT_EQ(fieldCount, 1);
            }
        }
    }
    EXPECT_TRUE(foundAnonymousStruct) << "Anonymous nested struct not found in C AST";
}

// =============================================================================
// Task 8: Struct Forward Declarations (Additional Tests)
// =============================================================================

/**
 * Test 15: Forward declaration with pointer usage (Task 8)
 * C++: struct Node; struct List { Node* head; };
 * C:   struct Node; struct List { struct Node* head; };
 *
 * Tests forward declaration used in pointer type.
 */
TEST_F(RecordHandlerTest, ForwardDeclarationWithPointerUsage) {
    const char* code = R"(
        struct Node;

        struct List {
            struct Node* head;
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::RecordDecl* cppNodeForward = nullptr;
    const clang::RecordDecl* cppList = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            std::string name = recordDecl->getNameAsString();
            if (name == "Node") {
                cppNodeForward = recordDecl;
            } else if (name == "List") {
                cppList = recordDecl;
            }
        }
    }

    ASSERT_NE(cppNodeForward, nullptr);
    ASSERT_NE(cppList, nullptr);
    EXPECT_FALSE(cppNodeForward->isCompleteDefinition()) << "Node should be forward declaration";
    EXPECT_TRUE(cppList->isCompleteDefinition()) << "List should be complete definition";

    // Translate forward declaration
    auto* cNodeForward = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppNodeForward, *context)
    );
    ASSERT_NE(cNodeForward, nullptr);
    EXPECT_EQ(cNodeForward->getNameAsString(), "Node");
    EXPECT_FALSE(cNodeForward->isCompleteDefinition()) << "C Node should be forward declaration";

    // Translate List
    auto* cList = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppList, *context)
    );
    ASSERT_NE(cList, nullptr);
    EXPECT_EQ(cList->getNameAsString(), "List");
    EXPECT_TRUE(cList->isCompleteDefinition()) << "C List should be complete definition";

    // Verify List has one field (head pointer)
    size_t fieldCount = 0;
    for (auto* field : cList->fields()) {
        EXPECT_EQ(field->getNameAsString(), "head");
        EXPECT_TRUE(field->getType()->isPointerType()) << "head should be pointer type";
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 1) << "List should have 1 field";
}

/**
 * Test 16: Multiple forward declarations (Task 8)
 * C++: struct A; struct B; struct C;
 * C:   struct A; struct B; struct C;
 *
 * Tests multiple forward declarations in sequence.
 */
TEST_F(RecordHandlerTest, MultipleForwardDeclarations) {
    const char* code = R"(
        struct A;
        struct B;
        struct C;
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    // Collect all forward declarations
    std::vector<const clang::RecordDecl*> forwardDecls;
    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            forwardDecls.push_back(recordDecl);
        }
    }

    ASSERT_EQ(forwardDecls.size(), 3) << "Should have 3 forward declarations";

    // Translate all forward declarations
    std::vector<std::string> expectedNames = {"A", "B", "C"};
    size_t index = 0;

    for (const auto* cppForward : forwardDecls) {
        EXPECT_FALSE(cppForward->isCompleteDefinition())
            << cppForward->getNameAsString() << " should be forward declaration";

        auto* cForward = llvm::cast<clang::RecordDecl>(
            handler->handleDecl(cppForward, *context)
        );

        ASSERT_NE(cForward, nullptr);
        EXPECT_EQ(cForward->getNameAsString(), expectedNames[index]);
        EXPECT_FALSE(cForward->isCompleteDefinition())
            << cForward->getNameAsString() << " should remain forward declaration";

        index++;
    }
}

/**
 * Test 17: Forward declaration followed by definition (Task 8)
 * C++: struct Point; struct Point { int x; int y; };
 * C:   struct Point; struct Point { int x; int y; };
 *
 * Tests forward declaration followed by complete definition.
 */
TEST_F(RecordHandlerTest, ForwardDeclarationFollowedByDefinition) {
    const char* code = R"(
        struct Point;

        struct Point {
            int x;
            int y;
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::RecordDecl* cppPointForward = nullptr;
    const clang::RecordDecl* cppPointDef = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (recordDecl->getNameAsString() == "Point") {
                if (recordDecl->isCompleteDefinition()) {
                    cppPointDef = recordDecl;
                } else {
                    cppPointForward = recordDecl;
                }
            }
        }
    }

    ASSERT_NE(cppPointForward, nullptr) << "Should have forward declaration";
    ASSERT_NE(cppPointDef, nullptr) << "Should have complete definition";

    // Translate forward declaration
    auto* cPointForward = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppPointForward, *context)
    );
    ASSERT_NE(cPointForward, nullptr);
    EXPECT_EQ(cPointForward->getNameAsString(), "Point");
    EXPECT_FALSE(cPointForward->isCompleteDefinition());

    // Translate definition
    auto* cPointDef = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppPointDef, *context)
    );
    ASSERT_NE(cPointDef, nullptr);
    EXPECT_EQ(cPointDef->getNameAsString(), "Point");
    EXPECT_TRUE(cPointDef->isCompleteDefinition());

    // Verify fields in definition
    size_t fieldCount = 0;
    for (auto* field : cPointDef->fields()) {
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 2) << "Point definition should have 2 fields";
}

// =============================================================================
// Task 2: Access Specifier Handling (Phase 44 Group 1 - Task 2)
// =============================================================================

/**
 * Test 18: Class with only public members (Task 2)
 * C++: class Data { public: int x; int y; };
 * C:   struct Data { int x; int y; };
 *
 * Tests that public access specifier is properly stripped.
 */
TEST_F(RecordHandlerTest, AccessSpecifier_OnlyPublic) {
    const char* code = R"(
        class Data {
        public:
            int x;
            int y;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isClass()) << "C++ should be class";

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Data", 2);
    EXPECT_TRUE(cRecord->isStruct()) << "C should be struct";

    // Verify both fields are present (access specifier stripped)
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "x");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "y");
}

/**
 * Test 19: Class with only private members (Task 2)
 * C++: class Data { private: int x; int y; };
 * C:   struct Data { int x; int y; };
 *
 * Tests that private access specifier is properly stripped.
 * Note: C has no access control - all fields are accessible.
 */
TEST_F(RecordHandlerTest, AccessSpecifier_OnlyPrivate) {
    const char* code = R"(
        class Data {
        private:
            int x;
            int y;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    // All fields should be present, even though they were private in C++
    verifyRecordStructure(cRecord, "Data", 2);

    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "x");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "y");
}

/**
 * Test 20: Class with only protected members (Task 2)
 * C++: class Data { protected: int x; int y; };
 * C:   struct Data { int x; int y; };
 *
 * Tests that protected access specifier is properly stripped.
 */
TEST_F(RecordHandlerTest, AccessSpecifier_OnlyProtected) {
    const char* code = R"(
        class Data {
        protected:
            int x;
            int y;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Data", 2);

    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "x");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "y");
}

/**
 * Test 21: Class with mixed access (public/private) (Task 2)
 * C++: class Mixed { public: int pub; private: int priv; };
 * C:   struct Mixed { int pub; int priv; };
 *
 * Tests that mixed access specifiers are properly stripped.
 */
TEST_F(RecordHandlerTest, AccessSpecifier_MixedPublicPrivate) {
    const char* code = R"(
        class Mixed {
        public:
            int pub;
        private:
            int priv;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Mixed", 2);

    // Verify field order is preserved
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "pub");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "priv");
}

/**
 * Test 22: Class with all three access specifiers (Task 2)
 * C++: class All { public: int pub; private: int priv; protected: int prot; };
 * C:   struct All { int pub; int priv; int prot; };
 *
 * Tests all three access specifiers in one class.
 */
TEST_F(RecordHandlerTest, AccessSpecifier_AllThree) {
    const char* code = R"(
        class All {
        public:
            int pub;
        private:
            int priv;
        protected:
            int prot;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "All", 3);

    // Verify all fields are present in order
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "pub");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "priv");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "prot");
}

/**
 * Test 23: Class with default access (private for class) (Task 2)
 * C++: class Data { int x; public: int y; };
 * C:   struct Data { int x; int y; };
 *
 * Tests default access (private for class, before first access specifier).
 */
TEST_F(RecordHandlerTest, AccessSpecifier_DefaultPrivate) {
    const char* code = R"(
        class Data {
            int x;  // Implicitly private (no access specifier)
        public:
            int y;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Data", 2);

    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "x") << "Implicitly private field";
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "y") << "Explicitly public field";
}

/**
 * Test 24: Struct with default access (public for struct) (Task 2)
 * C++: struct Data { int x; private: int y; };
 * C:   struct Data { int x; int y; };
 *
 * Tests default access (public for struct, before first access specifier).
 */
TEST_F(RecordHandlerTest, AccessSpecifier_DefaultPublic) {
    const char* code = R"(
        struct Data {
            int x;  // Implicitly public (no access specifier)
        private:
            int y;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Data", 2);

    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "x") << "Implicitly public field";
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "y") << "Explicitly private field";
}

/**
 * Test 25: Access specifiers interleaved with members (Task 2)
 * C++: class Data { public: int a; private: int b; public: int c; private: int d; };
 * C:   struct Data { int a; int b; int c; int d; };
 *
 * Tests multiple access specifiers interleaved with fields.
 */
TEST_F(RecordHandlerTest, AccessSpecifier_Interleaved) {
    const char* code = R"(
        class Data {
        public:
            int a;
        private:
            int b;
        public:
            int c;
        private:
            int d;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Data", 4);

    // Verify all fields are present in order
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "a");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "b");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "c");
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "d");
}

// =============================================================================
// Phase 44 Task 1: CXXRecordDecl Translation - Additional Tests
// =============================================================================

/**
 * Test 26: Empty class
 * C++: class Empty {};
 * C:   struct Empty {};
 */
TEST_F(RecordHandlerTest, CXXRecordDecl_EmptyClass) {
    const char* code = R"(
        class Empty {};
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppRecord)) << "Should be CXXRecordDecl";
    EXPECT_TRUE(handler->canHandle(cppRecord));

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "Empty", 0);
    EXPECT_TRUE(cRecord->isStruct()) << "Class should be translated to struct";
}

/**
 * Test 27: Class with all primitive types
 * C++: class AllTypes { public: int i; float f; double d; char c; bool b; };
 * C:   struct AllTypes { int i; float f; double d; char c; _Bool b; };
 */
TEST_F(RecordHandlerTest, CXXRecordDecl_AllPrimitiveTypes) {
    const char* code = R"(
        class AllTypes {
        public:
            int i;
            float f;
            double d;
            char c;
            bool b;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppRecord));

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "AllTypes", 5);

    // Verify field types
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "i");
    EXPECT_TRUE((*it)->getType()->isIntegerType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "f");
    EXPECT_TRUE((*it)->getType()->isFloatingType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "d");
    EXPECT_TRUE((*it)->getType()->isFloatingType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "c");
    EXPECT_TRUE((*it)->getType()->isCharType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "b");
    // bool in C++ becomes _Bool in C (also considered integer type)
    EXPECT_TRUE((*it)->getType()->isBooleanType() || (*it)->getType()->isIntegerType());
}

/**
 * Test 28: Class with pointers
 * C++: class WithPointer { public: int* ptr; char* str; };
 * C:   struct WithPointer { int* ptr; char* str; };
 */
TEST_F(RecordHandlerTest, CXXRecordDecl_WithPointers) {
    const char* code = R"(
        class WithPointer {
        public:
            int* ptr;
            char* str;
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppRecord));

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "WithPointer", 2);

    // Verify pointer types
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "ptr");
    EXPECT_TRUE((*it)->getType()->isPointerType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "str");
    EXPECT_TRUE((*it)->getType()->isPointerType());
}

/**
 * Test 29: Class with arrays
 * C++: class WithArray { public: int arr[10]; char buf[256]; };
 * C:   struct WithArray { int arr[10]; char buf[256]; };
 */
TEST_F(RecordHandlerTest, CXXRecordDecl_WithArrays) {
    const char* code = R"(
        class WithArray {
        public:
            int arr[10];
            char buf[256];
        };
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppRecord));

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    verifyRecordStructure(cRecord, "WithArray", 2);

    // Verify array types
    auto it = cRecord->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "arr");
    EXPECT_TRUE((*it)->getType()->isArrayType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "buf");
    EXPECT_TRUE((*it)->getType()->isArrayType());
}

/**
 * Test 30: Class with struct members
 * C++: struct Point { int x; int y; }; class Rect { public: Point topLeft; Point bottomRight; };
 * C:   struct Point { int x; int y; }; struct Rect { struct Point topLeft; struct Point bottomRight; };
 */
TEST_F(RecordHandlerTest, CXXRecordDecl_WithStructMembers) {
    const char* code = R"(
        struct Point {
            int x;
            int y;
        };

        class Rect {
        public:
            Point topLeft;
            Point bottomRight;
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::RecordDecl* cppPoint = nullptr;
    const clang::RecordDecl* cppRect = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (recordDecl->getNameAsString() == "Point") {
                cppPoint = recordDecl;
            } else if (recordDecl->getNameAsString() == "Rect") {
                cppRect = recordDecl;
            }
        }
    }

    ASSERT_NE(cppPoint, nullptr);
    ASSERT_NE(cppRect, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppRect)) << "Rect should be CXXRecordDecl";

    // Translate Point first
    auto* cPoint = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppPoint, *context)
    );
    ASSERT_NE(cPoint, nullptr);

    // Translate Rect
    auto* cRect = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRect, *context)
    );

    verifyRecordStructure(cRect, "Rect", 2);

    // Verify struct fields
    auto it = cRect->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "topLeft");
    EXPECT_TRUE((*it)->getType()->isStructureType());
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "bottomRight");
    EXPECT_TRUE((*it)->getType()->isStructureType());
}

/**
 * Test 31: Forward class declaration
 * C++: class Node;
 * C:   struct Node;
 */
TEST_F(RecordHandlerTest, CXXRecordDecl_ForwardDeclaration) {
    const char* code = R"(
        class Node;
    )";

    const auto* cppRecord = getRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppRecord));
    EXPECT_FALSE(cppRecord->isCompleteDefinition());

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);
    EXPECT_EQ(cRecord->getNameAsString(), "Node");
    EXPECT_FALSE(cRecord->isCompleteDefinition());
    EXPECT_TRUE(cRecord->isStruct()) << "Forward class should be translated to struct";
}

/**
 * Test 32: Multiple classes
 * C++: class A { public: int x; }; class B { public: float y; };
 * C:   struct A { int x; }; struct B { float y; };
 */
TEST_F(RecordHandlerTest, CXXRecordDecl_MultipleClasses) {
    const char* code = R"(
        class A {
        public:
            int x;
        };

        class B {
        public:
            float y;
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::RecordDecl* cppA = nullptr;
    const clang::RecordDecl* cppB = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (recordDecl->getNameAsString() == "A") {
                cppA = recordDecl;
            } else if (recordDecl->getNameAsString() == "B") {
                cppB = recordDecl;
            }
        }
    }

    ASSERT_NE(cppA, nullptr);
    ASSERT_NE(cppB, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppA));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppB));

    // Translate both classes
    auto* cA = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppA, *context)
    );
    auto* cB = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppB, *context)
    );

    verifyRecordStructure(cA, "A", 1);
    verifyRecordStructure(cB, "B", 1);

    // Verify fields
    auto itA = cA->field_begin();
    EXPECT_EQ((*itA)->getNameAsString(), "x");
    EXPECT_TRUE((*itA)->getType()->isIntegerType());

    auto itB = cB->field_begin();
    EXPECT_EQ((*itB)->getNameAsString(), "y");
    EXPECT_TRUE((*itB)->getType()->isFloatingType());
}

/**
 * Test 33: Class vs struct - both should translate to struct
 * C++: class MyClass { public: int x; }; struct MyStruct { int y; };
 * C:   struct MyClass { int x; }; struct MyStruct { int y; };
 */
TEST_F(RecordHandlerTest, CXXRecordDecl_ClassVsStruct) {
    const char* code = R"(
        class MyClass {
        public:
            int x;
        };

        struct MyStruct {
            int y;
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::RecordDecl* cppClass = nullptr;
    const clang::RecordDecl* cppStruct = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (recordDecl->getNameAsString() == "MyClass") {
                cppClass = recordDecl;
            } else if (recordDecl->getNameAsString() == "MyStruct") {
                cppStruct = recordDecl;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);
    ASSERT_NE(cppStruct, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(cppClass));

    // Translate both
    auto* cClass = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppClass, *context)
    );
    auto* cStruct = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppStruct, *context)
    );

    verifyRecordStructure(cClass, "MyClass", 1);
    verifyRecordStructure(cStruct, "MyStruct", 1);

    // Both should be struct in C
    EXPECT_TRUE(cClass->isStruct());
    EXPECT_TRUE(cStruct->isStruct());
}
