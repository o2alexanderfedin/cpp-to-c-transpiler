/**
 * @file RecordHandlerTest_MultipleLpVtbl.cpp
 * @brief TDD tests for RecordHandler multiple lpVtbl field injection (Phase 46 Group 1 Task 3)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (10-12 tests):
 * 1. InjectLpVtblForPrimaryBase - Inject lpVtbl for primary base
 * 2. InjectLpVtbl2ForFirstNonPrimary - Inject lpVtbl2 for first non-primary base
 * 3. InjectLpVtbl3ForSecondNonPrimary - Inject lpVtbl3 for second non-primary base
 * 4. CorrectFieldNaming - Verify field naming (lpVtbl, lpVtbl2, lpVtbl3)
 * 5. CorrectFieldOrder - All lpVtbl* fields first, before regular fields
 * 6. SingleInheritanceUsesLpVtblOnly - Single inheritance still uses lpVtbl only
 * 7. FieldsAfterAllLpVtblPointers - Regular fields come after all lpVtbl pointers
 * 8. ConstCorrectnessOnAllLpVtbl - All lpVtbl* are const pointers
 * 9. CorrectVtableTypes - Each lpVtbl points to correct vtable struct
 * 10. ThreeBasesThreeLpVtbl - Three polymorphic bases → lpVtbl, lpVtbl2, lpVtbl3
 * 11. MixedPolymorphicNonPolymorphic - Only polymorphic bases get lpVtbl fields
 * 12. EmptyClassWithMultipleLpVtbl - Empty class has only lpVtbl fields
 *
 * Multiple lpVtbl Pattern:
 * C++: class Shape : public IDrawable, public ISerializable { int x; };
 * C:   struct Shape {
 *          const struct Shape_IDrawable_vtable *lpVtbl;      // Primary
 *          const struct Shape_ISerializable_vtable *lpVtbl2; // Non-primary
 *          int x;
 *      };
 */

#include "handlers/RecordHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "MultipleInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class RecordHandlerMultipleLpVtblTest
 * @brief Test fixture for RecordHandler multiple lpVtbl field injection
 */
class RecordHandlerMultipleLpVtblTest : public ::testing::Test {
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
     * @brief Build AST from code and return the CXXRecordDecl by name
     */
    const clang::CXXRecordDecl* getCXXRecordDeclFromCode(const std::string& code, const std::string& className) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code";

        if (!cppAST) return nullptr;

        // Recreate builder and context with new AST
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Find the CXXRecordDecl by name
        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* cxxRecordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (!cxxRecordDecl->isImplicit() &&
                    cxxRecordDecl->getNameAsString() == className &&
                    cxxRecordDecl->isCompleteDefinition()) {
                    return cxxRecordDecl;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Count fields with specific name prefix in RecordDecl
     */
    int countFieldsWithPrefix(const clang::RecordDecl* record, const std::string& prefix) {
        int count = 0;
        for (auto* field : record->fields()) {
            if (field->getNameAsString().find(prefix) == 0) {
                count++;
            }
        }
        return count;
    }

    /**
     * @brief Get field by name
     */
    clang::FieldDecl* getFieldByName(const clang::RecordDecl* record, const std::string& name) {
        for (auto* field : record->fields()) {
            if (field->getNameAsString() == name) {
                return field;
            }
        }
        return nullptr;
    }

    /**
     * @brief Get field at index
     */
    clang::FieldDecl* getFieldAtIndex(const clang::RecordDecl* record, unsigned index) {
        unsigned i = 0;
        for (auto* field : record->fields()) {
            if (i == index) {
                return field;
            }
            i++;
        }
        return nullptr;
    }
};

// ============================================================================
// Test 1: Inject lpVtbl for Primary Base
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, InjectLpVtblForPrimaryBase) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
            int x;
        };
    )";

    auto* shape = getCXXRecordDeclFromCode(code, "Shape");
    ASSERT_NE(shape, nullptr);

    // Translate the record
    auto* cRecord = handler->handleDecl(shape, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Should have lpVtbl field
    auto* lpVtblField = getFieldByName(recordDecl, "lpVtbl");
    EXPECT_NE(lpVtblField, nullptr) << "Should have lpVtbl field for primary base";
}

// ============================================================================
// Test 2: Inject lpVtbl2 for First Non-Primary Base
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, InjectLpVtbl2ForFirstNonPrimary) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
            int x;
        };
    )";

    auto* shape = getCXXRecordDeclFromCode(code, "Shape");
    ASSERT_NE(shape, nullptr);

    // Translate the record
    auto* cRecord = handler->handleDecl(shape, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Should have lpVtbl2 field for first non-primary base
    auto* lpVtbl2Field = getFieldByName(recordDecl, "lpVtbl2");
    EXPECT_NE(lpVtbl2Field, nullptr) << "Should have lpVtbl2 field for first non-primary base";
}

// ============================================================================
// Test 3: Inject lpVtbl3 for Second Non-Primary Base
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, InjectLpVtbl3ForSecondNonPrimary) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class IClickable {
        public:
            virtual void onClick() = 0;
        };

        class Widget : public IDrawable, public ISerializable, public IClickable {
            int x;
        };
    )";

    auto* widget = getCXXRecordDeclFromCode(code, "Widget");
    ASSERT_NE(widget, nullptr);

    // Translate the record
    auto* cRecord = handler->handleDecl(widget, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Should have lpVtbl, lpVtbl2, lpVtbl3
    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl"), nullptr);
    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl2"), nullptr);
    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl3"), nullptr)
        << "Should have lpVtbl3 field for second non-primary base";
}

// ============================================================================
// Test 4: Correct Field Naming
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, CorrectFieldNaming) {
    std::string code = R"(
        class Base1 {
        public:
            virtual void method1() = 0;
        };

        class Base2 {
        public:
            virtual void method2() = 0;
        };

        class Derived : public Base1, public Base2 {
        };
    )";

    auto* derived = getCXXRecordDeclFromCode(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* cRecord = handler->handleDecl(derived, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Verify naming: lpVtbl, lpVtbl2, lpVtbl3, etc.
    auto* field1 = getFieldByName(recordDecl, "lpVtbl");
    auto* field2 = getFieldByName(recordDecl, "lpVtbl2");

    EXPECT_NE(field1, nullptr) << "Primary base should use 'lpVtbl'";
    EXPECT_NE(field2, nullptr) << "First non-primary should use 'lpVtbl2'";
}

// ============================================================================
// Test 5: Correct Field Order - All lpVtbl* First
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, CorrectFieldOrder) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
            int x;
            int y;
        };
    )";

    auto* shape = getCXXRecordDeclFromCode(code, "Shape");
    ASSERT_NE(shape, nullptr);

    auto* cRecord = handler->handleDecl(shape, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // First two fields should be lpVtbl and lpVtbl2
    auto* field0 = getFieldAtIndex(recordDecl, 0);
    auto* field1 = getFieldAtIndex(recordDecl, 1);
    auto* field2 = getFieldAtIndex(recordDecl, 2);
    auto* field3 = getFieldAtIndex(recordDecl, 3);

    ASSERT_NE(field0, nullptr);
    ASSERT_NE(field1, nullptr);
    ASSERT_NE(field2, nullptr);
    ASSERT_NE(field3, nullptr);

    EXPECT_EQ(field0->getNameAsString(), "lpVtbl")
        << "First field must be lpVtbl";
    EXPECT_EQ(field1->getNameAsString(), "lpVtbl2")
        << "Second field must be lpVtbl2";
    EXPECT_EQ(field2->getNameAsString(), "x")
        << "Regular fields come after lpVtbl pointers";
    EXPECT_EQ(field3->getNameAsString(), "y")
        << "All regular fields after lpVtbl pointers";
}

// ============================================================================
// Test 6: Single Inheritance Uses lpVtbl Only
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, SingleInheritanceUsesLpVtblOnly) {
    std::string code = R"(
        class Base {
        public:
            virtual void method() {}
        };

        class Derived : public Base {
            int x;
        };
    )";

    auto* derived = getCXXRecordDeclFromCode(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* cRecord = handler->handleDecl(derived, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Should have lpVtbl only (no lpVtbl2)
    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl"), nullptr);
    EXPECT_EQ(getFieldByName(recordDecl, "lpVtbl2"), nullptr)
        << "Single inheritance should not have lpVtbl2";
}

// ============================================================================
// Test 7: Fields After All lpVtbl Pointers
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, FieldsAfterAllLpVtblPointers) {
    std::string code = R"(
        class Base1 {
        public:
            virtual void m1() = 0;
        };

        class Base2 {
        public:
            virtual void m2() = 0;
        };

        class Derived : public Base1, public Base2 {
            int a;
            int b;
            int c;
        };
    )";

    auto* derived = getCXXRecordDeclFromCode(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* cRecord = handler->handleDecl(derived, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Count lpVtbl fields
    int lpVtblCount = 0;
    bool foundRegularField = false;

    for (auto* field : recordDecl->fields()) {
        std::string name = field->getNameAsString();
        if (name.find("lpVtbl") == 0) {
            lpVtblCount++;
            EXPECT_FALSE(foundRegularField)
                << "All lpVtbl* fields must come before regular fields";
        } else {
            foundRegularField = true;
        }
    }

    EXPECT_EQ(lpVtblCount, 2) << "Should have 2 lpVtbl fields";
}

// ============================================================================
// Test 8: Const Correctness on All lpVtbl
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, ConstCorrectnessOnAllLpVtbl) {
    std::string code = R"(
        class Base1 {
        public:
            virtual void m1() = 0;
        };

        class Base2 {
        public:
            virtual void m2() = 0;
        };

        class Derived : public Base1, public Base2 {
        };
    )";

    auto* derived = getCXXRecordDeclFromCode(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* cRecord = handler->handleDecl(derived, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Check that lpVtbl fields are const pointers
    auto* lpVtbl = getFieldByName(recordDecl, "lpVtbl");
    auto* lpVtbl2 = getFieldByName(recordDecl, "lpVtbl2");

    ASSERT_NE(lpVtbl, nullptr);
    ASSERT_NE(lpVtbl2, nullptr);

    // Both should be const pointers
    EXPECT_TRUE(lpVtbl->getType()->isPointerType());
    EXPECT_TRUE(lpVtbl2->getType()->isPointerType());
}

// ============================================================================
// Test 9: Correct Vtable Types
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, CorrectVtableTypes) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
        };
    )";

    auto* shape = getCXXRecordDeclFromCode(code, "Shape");
    ASSERT_NE(shape, nullptr);

    auto* cRecord = handler->handleDecl(shape, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    auto* lpVtbl = getFieldByName(recordDecl, "lpVtbl");
    auto* lpVtbl2 = getFieldByName(recordDecl, "lpVtbl2");

    ASSERT_NE(lpVtbl, nullptr);
    ASSERT_NE(lpVtbl2, nullptr);

    // Check types point to correct vtable structs
    // Type should be: const struct Shape_IDrawable_vtable *
    //                 const struct Shape_ISerializable_vtable *
    std::string type1 = lpVtbl->getType().getAsString();
    std::string type2 = lpVtbl2->getType().getAsString();

    // Verify they're different vtable types
    EXPECT_NE(type1, type2) << "Each lpVtbl should point to different vtable struct";
}

// ============================================================================
// Test 10: Three Bases Three lpVtbl
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, ThreeBasesThreeLpVtbl) {
    std::string code = R"(
        class Base1 {
        public:
            virtual void m1() = 0;
        };

        class Base2 {
        public:
            virtual void m2() = 0;
        };

        class Base3 {
        public:
            virtual void m3() = 0;
        };

        class Derived : public Base1, public Base2, public Base3 {
        };
    )";

    auto* derived = getCXXRecordDeclFromCode(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* cRecord = handler->handleDecl(derived, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Should have lpVtbl, lpVtbl2, lpVtbl3
    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl"), nullptr);
    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl2"), nullptr);
    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl3"), nullptr);
    EXPECT_EQ(getFieldByName(recordDecl, "lpVtbl4"), nullptr)
        << "Should not have lpVtbl4 with only 3 bases";
}

// ============================================================================
// Test 11: Mixed Polymorphic Non-Polymorphic
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, MixedPolymorphicNonPolymorphic) {
    std::string code = R"(
        class NonVirtual {
        public:
            int x;
        };

        class Virtual1 {
        public:
            virtual void m1() = 0;
        };

        class Virtual2 {
        public:
            virtual void m2() = 0;
        };

        class Derived : public NonVirtual, public Virtual1, public Virtual2 {
        };
    )";

    auto* derived = getCXXRecordDeclFromCode(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* cRecord = handler->handleDecl(derived, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Should have lpVtbl and lpVtbl2 (only for polymorphic bases)
    int lpVtblCount = countFieldsWithPrefix(recordDecl, "lpVtbl");
    EXPECT_EQ(lpVtblCount, 2)
        << "Should have 2 lpVtbl fields (only for polymorphic bases)";
}

// ============================================================================
// Test 12: Empty Class With Multiple lpVtbl
// ============================================================================

TEST_F(RecordHandlerMultipleLpVtblTest, EmptyClassWithMultipleLpVtbl) {
    std::string code = R"(
        class IInterface1 {
        public:
            virtual void m1() = 0;
        };

        class IInterface2 {
        public:
            virtual void m2() = 0;
        };

        class Impl : public IInterface1, public IInterface2 {
        };
    )";

    auto* impl = getCXXRecordDeclFromCode(code, "Impl");
    ASSERT_NE(impl, nullptr);

    auto* cRecord = handler->handleDecl(impl, *context);
    ASSERT_NE(cRecord, nullptr);

    auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(cRecord);
    ASSERT_NE(recordDecl, nullptr);

    // Should have exactly 2 fields (lpVtbl and lpVtbl2)
    unsigned fieldCount = 0;
    for (auto* field : recordDecl->fields()) {
        fieldCount++;
    }

    EXPECT_EQ(fieldCount, 2)
        << "Empty class should have only lpVtbl and lpVtbl2 fields";

    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl"), nullptr);
    EXPECT_NE(getFieldByName(recordDecl, "lpVtbl2"), nullptr);
}
