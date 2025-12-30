/**
 * @file RecordHandlerTest_lpVtbl.cpp
 * @brief TDD tests for RecordHandler lpVtbl field injection (Phase 45 Task 3)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (6-8 tests):
 * 1. lpVtblIsFirstField - Verify lpVtbl is first field in polymorphic class
 * 2. lpVtblCorrectType - Verify lpVtbl has correct type (const struct ClassName_vtable *)
 * 3. lpVtblConstPointer - Verify lpVtbl is const pointer
 * 4. lpVtblSingleInheritance - Base lpVtbl first in derived class
 * 5. lpVtblWithMultipleFields - lpVtbl first, other fields follow
 * 6. lpVtblEmptyPolymorphicClass - Empty class with only lpVtbl
 * 7. lpVtblFieldAccessWorks - Field access still works with lpVtbl present
 * 8. NoLpVtblForNonPolymorphic - Non-polymorphic classes don't get lpVtbl
 *
 * lpVtbl Pattern (COM/DCOM ABI):
 * C++: class Animal { int age; public: virtual void speak(); };
 * C:   struct Animal {
 *          const struct Animal_vtable *lpVtbl;  // MUST be first!
 *          int age;
 *      };
 */

#include "dispatch/RecordHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class RecordHandlerLpVtblTest
 * @brief Test fixture for RecordHandler lpVtbl field injection
 */
class RecordHandlerLpVtblTest : public ::testing::Test {
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
     * @brief Build AST from code and return the first CXXRecordDecl
     */
    const clang::CXXRecordDecl* getCXXRecordDeclFromCode(const std::string& code) {
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

        // Find the first CXXRecordDecl
        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* cxxRecordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                // Skip implicit declarations
                if (!cxxRecordDecl->isImplicit()) {
                    return cxxRecordDecl;
                }
            }
        }

        return nullptr;
    }

    /**
     * @brief Find a RecordDecl by name in the C translation unit
     */
    clang::RecordDecl* findCRecordByName(const std::string& name) {
        auto& cCtx = cAST->getASTContext();
        auto* cTU = cCtx.getTranslationUnitDecl();

        for (auto* decl : cTU->decls()) {
            if (auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(decl)) {
                if (recordDecl->getNameAsString() == name) {
                    return recordDecl;
                }
            }
        }

        return nullptr;
    }
};

// =============================================================================
// Test 1: lpVtbl is first field in polymorphic class
// =============================================================================

/**
 * Test 1: lpVtbl is first field
 * C++: class Animal { int age; public: virtual void speak(); };
 * C:   struct Animal {
 *          const struct Animal_vtable *lpVtbl;  // MUST be first!
 *          int age;
 *      };
 */
TEST_F(RecordHandlerLpVtblTest, lpVtblIsFirstField) {
    const char* code = R"(
        class Animal {
            int age;
        public:
            virtual void speak();
        };
    )";

    const auto* cxxRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cxxRecord, nullptr);
    EXPECT_TRUE(cxxRecord->isPolymorphic()) << "Animal should be polymorphic";

    // Translate to C
    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cxxRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);
    EXPECT_EQ(cRecord->getNameAsString(), "Animal");

    // Verify lpVtbl is the FIRST field
    auto fieldIt = cRecord->field_begin();
    ASSERT_NE(fieldIt, cRecord->field_end()) << "Struct should have fields";

    const auto* firstField = *fieldIt;
    EXPECT_EQ(firstField->getNameAsString(), "lpVtbl")
        << "First field MUST be lpVtbl for COM/DCOM ABI compatibility";

    // Verify second field is age
    ++fieldIt;
    ASSERT_NE(fieldIt, cRecord->field_end()) << "Should have second field";
    const auto* secondField = *fieldIt;
    EXPECT_EQ(secondField->getNameAsString(), "age");

    // Count fields: should be 2 (lpVtbl + age)
    size_t fieldCount = 0;
    for (auto* field : cRecord->fields()) {
        (void)field;
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 2) << "Should have 2 fields: lpVtbl and age";
}

// =============================================================================
// Test 2: lpVtbl has correct type
// =============================================================================

/**
 * Test 2: lpVtbl has correct type (const struct ClassName_vtable *)
 * C++: class Shape { public: virtual double area() = 0; };
 * C:   struct Shape {
 *          const struct Shape_vtable *lpVtbl;
 *      };
 */
TEST_F(RecordHandlerLpVtblTest, lpVtblCorrectType) {
    const char* code = R"(
        class Shape {
        public:
            virtual double area() = 0;
        };
    )";

    const auto* cxxRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cxxRecord, nullptr);
    EXPECT_TRUE(cxxRecord->isPolymorphic());

    // Translate to C
    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cxxRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);

    // Get first field (should be lpVtbl)
    auto fieldIt = cRecord->field_begin();
    ASSERT_NE(fieldIt, cRecord->field_end());
    const auto* lpVtblField = *fieldIt;

    EXPECT_EQ(lpVtblField->getNameAsString(), "lpVtbl");

    // Verify type: const struct Shape_vtable *
    auto fieldType = lpVtblField->getType();

    // Should be pointer type
    EXPECT_TRUE(fieldType->isPointerType()) << "lpVtbl should be pointer type";

    if (fieldType->isPointerType()) {
        // Get pointee type
        auto pointeeType = fieldType->getPointeeType();

        // Pointee should be const-qualified
        EXPECT_TRUE(pointeeType.isConstQualified())
            << "lpVtbl should point to const vtable";

        // Pointee should be struct type
        EXPECT_TRUE(pointeeType->isStructureType())
            << "lpVtbl should point to struct";

        // Get the struct and verify it's Shape_vtable
        if (const auto* recordType = pointeeType->getAs<clang::RecordType>()) {
            const auto* vtableStruct = recordType->getDecl();
            EXPECT_EQ(vtableStruct->getNameAsString(), "Shape_vtable")
                << "lpVtbl should point to Shape_vtable";
        }
    }
}

// =============================================================================
// Test 3: lpVtbl is const pointer
// =============================================================================

/**
 * Test 3: lpVtbl is const pointer to const vtable
 * Type should be: const struct ClassName_vtable * (not const pointer itself)
 * The vtable struct is const, the pointer is not const (can be reassigned)
 */
TEST_F(RecordHandlerLpVtblTest, lpVtblConstPointer) {
    const char* code = R"(
        class Base {
        public:
            virtual void foo();
        };
    )";

    const auto* cxxRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cxxRecord, nullptr);
    EXPECT_TRUE(cxxRecord->isPolymorphic());

    // Translate to C
    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cxxRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);

    // Get lpVtbl field
    auto fieldIt = cRecord->field_begin();
    ASSERT_NE(fieldIt, cRecord->field_end());
    const auto* lpVtblField = *fieldIt;

    EXPECT_EQ(lpVtblField->getNameAsString(), "lpVtbl");

    auto fieldType = lpVtblField->getType();
    ASSERT_TRUE(fieldType->isPointerType());

    // The pointee (vtable struct) should be const
    auto pointeeType = fieldType->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified())
        << "Vtable struct should be const-qualified";

    // The pointer itself is NOT const (can be reassigned for polymorphism)
    // This is the COM pattern: const struct Base_vtable *lpVtbl;
    EXPECT_FALSE(fieldType.isConstQualified())
        << "Pointer itself should not be const (allows vtable reassignment)";
}

// =============================================================================
// Test 4: Single inheritance - base lpVtbl is first
// =============================================================================

/**
 * Test 4: Single inheritance - derived class embeds base lpVtbl correctly
 * C++: class Base { public: virtual void foo(); };
 *      class Derived : public Base { int x; public: virtual void bar(); };
 * C:   struct Derived {
 *          const struct Derived_vtable *lpVtbl;  // First field!
 *          int x;
 *      };
 */
TEST_F(RecordHandlerLpVtblTest, lpVtblSingleInheritance) {
    const char* code = R"(
        class Base {
        public:
            virtual void foo();
        };

        class Derived : public Base {
            int x;
        public:
            virtual void bar();
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

    const clang::CXXRecordDecl* cxxDerived = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* cxxRecordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (cxxRecordDecl->getNameAsString() == "Derived") {
                cxxDerived = cxxRecordDecl;
                break;
            }
        }
    }

    ASSERT_NE(cxxDerived, nullptr);
    EXPECT_TRUE(cxxDerived->isPolymorphic());

    // Translate Derived
    auto* cDerived = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cxxDerived, *context)
    );

    ASSERT_NE(cDerived, nullptr);

    // Verify lpVtbl is FIRST field (not embedded in base)
    auto fieldIt = cDerived->field_begin();
    ASSERT_NE(fieldIt, cDerived->field_end());

    const auto* firstField = *fieldIt;
    EXPECT_EQ(firstField->getNameAsString(), "lpVtbl")
        << "lpVtbl MUST be first field in derived class";

    // Verify it points to Derived_vtable (not Base_vtable)
    auto fieldType = firstField->getType();
    ASSERT_TRUE(fieldType->isPointerType());
    auto pointeeType = fieldType->getPointeeType();

    if (const auto* recordType = pointeeType->getAs<clang::RecordType>()) {
        const auto* vtableStruct = recordType->getDecl();
        EXPECT_EQ(vtableStruct->getNameAsString(), "Derived_vtable")
            << "Derived class should have its own vtable";
    }
}

// =============================================================================
// Test 5: lpVtbl with multiple fields
// =============================================================================

/**
 * Test 5: Multiple fields after lpVtbl
 * C++: class Data { int x; float y; char z; public: virtual void process(); };
 * C:   struct Data {
 *          const struct Data_vtable *lpVtbl;  // First!
 *          int x;
 *          float y;
 *          char z;
 *      };
 */
TEST_F(RecordHandlerLpVtblTest, lpVtblWithMultipleFields) {
    const char* code = R"(
        class Data {
            int x;
            float y;
            char z;
        public:
            virtual void process();
        };
    )";

    const auto* cxxRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cxxRecord, nullptr);
    EXPECT_TRUE(cxxRecord->isPolymorphic());

    // Translate to C
    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cxxRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);

    // Count fields: should be 4 (lpVtbl + x + y + z)
    size_t fieldCount = 0;
    for (auto* field : cRecord->fields()) {
        (void)field;
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 4) << "Should have 4 fields: lpVtbl, x, y, z";

    // Verify order: lpVtbl, x, y, z
    auto fieldIt = cRecord->field_begin();

    ASSERT_NE(fieldIt, cRecord->field_end());
    EXPECT_EQ((*fieldIt)->getNameAsString(), "lpVtbl");

    ++fieldIt;
    ASSERT_NE(fieldIt, cRecord->field_end());
    EXPECT_EQ((*fieldIt)->getNameAsString(), "x");

    ++fieldIt;
    ASSERT_NE(fieldIt, cRecord->field_end());
    EXPECT_EQ((*fieldIt)->getNameAsString(), "y");

    ++fieldIt;
    ASSERT_NE(fieldIt, cRecord->field_end());
    EXPECT_EQ((*fieldIt)->getNameAsString(), "z");
}

// =============================================================================
// Test 6: Empty class with only lpVtbl
// =============================================================================

/**
 * Test 6: Empty polymorphic class - only lpVtbl
 * C++: class Interface { public: virtual void execute() = 0; };
 * C:   struct Interface {
 *          const struct Interface_vtable *lpVtbl;
 *      };
 */
TEST_F(RecordHandlerLpVtblTest, lpVtblEmptyPolymorphicClass) {
    const char* code = R"(
        class Interface {
        public:
            virtual void execute() = 0;
        };
    )";

    const auto* cxxRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cxxRecord, nullptr);
    EXPECT_TRUE(cxxRecord->isPolymorphic());
    EXPECT_TRUE(cxxRecord->isAbstract()) << "Interface should be abstract";

    // Translate to C
    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cxxRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);

    // Should have exactly 1 field: lpVtbl
    size_t fieldCount = 0;
    for (auto* field : cRecord->fields()) {
        (void)field;
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 1) << "Empty interface should only have lpVtbl";

    // Verify it's lpVtbl
    auto fieldIt = cRecord->field_begin();
    ASSERT_NE(fieldIt, cRecord->field_end());
    EXPECT_EQ((*fieldIt)->getNameAsString(), "lpVtbl");
}

// =============================================================================
// Test 7: Field access works with lpVtbl present
// =============================================================================

/**
 * Test 7: Field access still works with lpVtbl
 * Verify that we can access regular fields after lpVtbl
 */
TEST_F(RecordHandlerLpVtblTest, lpVtblFieldAccessWorks) {
    const char* code = R"(
        class Widget {
            int width;
            int height;
        public:
            virtual void render();
        };
    )";

    const auto* cxxRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cxxRecord, nullptr);
    EXPECT_TRUE(cxxRecord->isPolymorphic());

    // Translate to C
    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cxxRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);

    // Find width and height fields
    bool foundWidth = false;
    bool foundHeight = false;

    for (auto* field : cRecord->fields()) {
        std::string name = field->getNameAsString();
        if (name == "width") {
            foundWidth = true;
            EXPECT_TRUE(field->getType()->isIntegerType());
        } else if (name == "height") {
            foundHeight = true;
            EXPECT_TRUE(field->getType()->isIntegerType());
        }
    }

    EXPECT_TRUE(foundWidth) << "Should have width field";
    EXPECT_TRUE(foundHeight) << "Should have height field";

    // Verify field count: 3 (lpVtbl + width + height)
    size_t fieldCount = 0;
    for (auto* field : cRecord->fields()) {
        (void)field;
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 3);
}

// =============================================================================
// Test 8: Non-polymorphic classes don't get lpVtbl
// =============================================================================

/**
 * Test 8: Non-polymorphic classes should NOT have lpVtbl
 * C++: class Plain { int x; public: void foo(); };  // No virtual methods
 * C:   struct Plain { int x; };  // No lpVtbl!
 */
TEST_F(RecordHandlerLpVtblTest, NoLpVtblForNonPolymorphic) {
    const char* code = R"(
        class Plain {
            int x;
        public:
            void foo();  // Not virtual!
        };
    )";

    const auto* cxxRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cxxRecord, nullptr);
    EXPECT_FALSE(cxxRecord->isPolymorphic())
        << "Plain class should NOT be polymorphic";

    // Translate to C
    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cxxRecord, *context)
    );

    ASSERT_NE(cRecord, nullptr);

    // Should have exactly 1 field: x (no lpVtbl!)
    size_t fieldCount = 0;
    for (auto* field : cRecord->fields()) {
        (void)field;
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 1) << "Non-polymorphic class should only have x field";

    // Verify it's x, not lpVtbl
    auto fieldIt = cRecord->field_begin();
    ASSERT_NE(fieldIt, cRecord->field_end());
    EXPECT_EQ((*fieldIt)->getNameAsString(), "x")
        << "First field should be x, NOT lpVtbl";
}
