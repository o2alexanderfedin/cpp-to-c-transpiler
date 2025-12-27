/**
 * @file MultipleInheritanceAnalyzerTest.cpp
 * @brief Unit tests for MultipleInheritanceAnalyzer
 *
 * Phase 46, Group 1, Task 1: Base Class Analysis
 * Tests: 10 tests covering all requirements
 */

#include "MultipleInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

/**
 * @class MultipleInheritanceAnalyzerTest
 * @brief Test fixture for MultipleInheritanceAnalyzer
 */
class MultipleInheritanceAnalyzerTest : public ::testing::Test {
protected:
    /**
     * @brief Helper to parse C++ code and get CXXRecordDecl by name
     */
    CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        auto AST = tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

        analyzer = std::make_unique<MultipleInheritanceAnalyzer>(AST->getASTContext());
        context = std::move(AST);

        for (auto* decl : context->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = dyn_cast<CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == className && record->isCompleteDefinition()) {
                    return record;
                }
            }
        }
        return nullptr;
    }

    std::unique_ptr<clang::ASTUnit> context;
    std::unique_ptr<MultipleInheritanceAnalyzer> analyzer;
};

// ============================================================================
// Test 1: Detect Multiple Polymorphic Bases
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, DetectMultiplePolymorphicBases) {
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
        public:
            void draw() override {}
            void serialize() override {}
        };
    )";

    auto* shape = getClass(code, "Shape");
    ASSERT_NE(shape, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(shape);

    EXPECT_EQ(bases.size(), 2) << "Should detect 2 polymorphic bases";
    EXPECT_TRUE(analyzer->hasMultiplePolymorphicBases(shape));
}

// ============================================================================
// Test 2: Identify Primary Base
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, IdentifyPrimaryBase) {
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

    auto* shape = getClass(code, "Shape");
    ASSERT_NE(shape, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(shape);
    ASSERT_EQ(bases.size(), 2);

    // First base should be primary
    EXPECT_TRUE(bases[0].IsPrimary) << "IDrawable should be primary base";
    EXPECT_EQ(bases[0].VtblFieldName, "lpVtbl");
    EXPECT_EQ(bases[0].VtblIndex, 0);

    // Primary base should match getPrimaryBase()
    auto* primaryBase = analyzer->getPrimaryBase(shape);
    EXPECT_EQ(primaryBase, bases[0].BaseDecl);
    EXPECT_EQ(primaryBase->getNameAsString(), "IDrawable");
}

// ============================================================================
// Test 3: Identify Non-Primary Bases
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, IdentifyNonPrimaryBases) {
    std::string code = R"(
        class Base1 { public: virtual void f1() {} };
        class Base2 { public: virtual void f2() {} };
        class Base3 { public: virtual void f3() {} };

        class Derived : public Base1, public Base2, public Base3 {
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(derived);
    ASSERT_EQ(bases.size(), 3);

    // First is primary
    EXPECT_TRUE(bases[0].IsPrimary);
    EXPECT_EQ(bases[0].VtblFieldName, "lpVtbl");

    // Second and third are non-primary
    EXPECT_FALSE(bases[1].IsPrimary);
    EXPECT_EQ(bases[1].VtblFieldName, "lpVtbl2");
    EXPECT_EQ(bases[1].VtblIndex, 1);

    EXPECT_FALSE(bases[2].IsPrimary);
    EXPECT_EQ(bases[2].VtblFieldName, "lpVtbl3");
    EXPECT_EQ(bases[2].VtblIndex, 2);

    // getNonPrimaryBases() should return 2 bases
    auto nonPrimary = analyzer->getNonPrimaryBases(derived);
    EXPECT_EQ(nonPrimary.size(), 2);
    EXPECT_EQ(nonPrimary[0]->getNameAsString(), "Base2");
    EXPECT_EQ(nonPrimary[1]->getNameAsString(), "Base3");
}

// ============================================================================
// Test 4: Calculate Base Offsets
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, CalculateBaseOffsets) {
    std::string code = R"(
        class Base1 { public: virtual void f1() {} };
        class Base2 { public: virtual void f2() {} };

        class Derived : public Base1, public Base2 {
            int field;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(derived);
    ASSERT_EQ(bases.size(), 2);

    // Primary base at offset 0
    EXPECT_EQ(bases[0].Offset, 0) << "Primary base should be at offset 0";

    // Non-primary base at non-zero offset
    EXPECT_GT(bases[1].Offset, 0) << "Non-primary base should be at offset > 0";

    // Verify calculateBaseOffset() returns same values
    auto* base1 = bases[0].BaseDecl;
    auto* base2 = bases[1].BaseDecl;

    EXPECT_EQ(analyzer->calculateBaseOffset(derived, base1), bases[0].Offset);
    EXPECT_EQ(analyzer->calculateBaseOffset(derived, base2), bases[1].Offset);
}

// ============================================================================
// Test 5: Single Inheritance No Change
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, SingleInheritanceNoChange) {
    std::string code = R"(
        class Base {
        public:
            virtual void method() {}
        };

        class Derived : public Base {
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(derived);

    // Should have exactly one base
    EXPECT_EQ(bases.size(), 1);
    EXPECT_TRUE(bases[0].IsPrimary);
    EXPECT_EQ(bases[0].VtblFieldName, "lpVtbl");
    EXPECT_EQ(bases[0].Offset, 0);

    // Should NOT have multiple polymorphic bases
    EXPECT_FALSE(analyzer->hasMultiplePolymorphicBases(derived));

    // getNonPrimaryBases should return empty
    auto nonPrimary = analyzer->getNonPrimaryBases(derived);
    EXPECT_EQ(nonPrimary.size(), 0);
}

// ============================================================================
// Test 6: Non-Polymorphic Bases Skipped
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, NonPolymorphicBasesSkipped) {
    std::string code = R"(
        class NonPolymorphic {
        public:
            void regularMethod() {}
        };

        class Polymorphic {
        public:
            virtual void virtualMethod() {}
        };

        class Derived : public NonPolymorphic, public Polymorphic {
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(derived);

    // Should only include polymorphic base
    EXPECT_EQ(bases.size(), 1);
    EXPECT_EQ(bases[0].BaseDecl->getNameAsString(), "Polymorphic");
    EXPECT_TRUE(bases[0].IsPrimary);
}

// ============================================================================
// Test 7: Mixed Polymorphic and Non-Polymorphic
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, MixedPolymorphicNonPolymorphic) {
    std::string code = R"(
        class NonPoly1 { int x; };
        class Poly1 { public: virtual void f1() {} };
        class NonPoly2 { int y; };
        class Poly2 { public: virtual void f2() {} };

        class Derived : public NonPoly1, public Poly1, public NonPoly2, public Poly2 {
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(derived);

    // Should only include 2 polymorphic bases
    EXPECT_EQ(bases.size(), 2);
    EXPECT_EQ(bases[0].BaseDecl->getNameAsString(), "Poly1");
    EXPECT_EQ(bases[1].BaseDecl->getNameAsString(), "Poly2");

    EXPECT_TRUE(bases[0].IsPrimary);
    EXPECT_FALSE(bases[1].IsPrimary);
}

// ============================================================================
// Test 8: Deep Inheritance Hierarchy
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, DeepInheritanceHierarchy) {
    std::string code = R"(
        class GrandBase1 {
        public:
            virtual void gf1() {}
        };

        class GrandBase2 {
        public:
            virtual void gf2() {}
        };

        class Parent1 : public GrandBase1 {
        };

        class Parent2 : public GrandBase2 {
        };

        class Child : public Parent1, public Parent2 {
        };
    )";

    auto* child = getClass(code, "Child");
    ASSERT_NE(child, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(child);

    // Should detect both polymorphic parents
    EXPECT_EQ(bases.size(), 2);
    EXPECT_EQ(bases[0].BaseDecl->getNameAsString(), "Parent1");
    EXPECT_EQ(bases[1].BaseDecl->getNameAsString(), "Parent2");

    EXPECT_TRUE(bases[0].IsPrimary);
    EXPECT_FALSE(bases[1].IsPrimary);
}

// ============================================================================
// Test 9: Empty Class With Multiple Bases
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, EmptyClassWithMultipleBases) {
    std::string code = R"(
        class IInterface1 {
        public:
            virtual void method1() = 0;
        };

        class IInterface2 {
        public:
            virtual void method2() = 0;
        };

        class EmptyImpl : public IInterface1, public IInterface2 {
        };
    )";

    auto* emptyImpl = getClass(code, "EmptyImpl");
    ASSERT_NE(emptyImpl, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(emptyImpl);

    // Should detect both bases even though class has no fields
    EXPECT_EQ(bases.size(), 2);
    EXPECT_TRUE(bases[0].IsPrimary);
    EXPECT_FALSE(bases[1].IsPrimary);
}

// ============================================================================
// Test 10: No Bases Returns Empty
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, NoBasesReturnsEmpty) {
    std::string code = R"(
        class Standalone {
        public:
            virtual void method() {}
        };
    )";

    auto* standalone = getClass(code, "Standalone");
    ASSERT_NE(standalone, nullptr);

    auto bases = analyzer->analyzePolymorphicBases(standalone);

    // Should return empty - no bases
    EXPECT_EQ(bases.size(), 0);
    EXPECT_FALSE(analyzer->hasMultiplePolymorphicBases(standalone));
    EXPECT_EQ(analyzer->getPrimaryBase(standalone), nullptr);
    EXPECT_EQ(analyzer->getNonPrimaryBases(standalone).size(), 0);
}

// ============================================================================
// Test 11: Null Input Handling
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, NullInputHandling) {
    std::string code = "class Dummy {};";
    auto* dummy = getClass(code, "Dummy");
    ASSERT_NE(dummy, nullptr);

    // These should not crash with null input
    auto bases = analyzer->analyzePolymorphicBases(nullptr);
    EXPECT_EQ(bases.size(), 0);

    EXPECT_FALSE(analyzer->hasMultiplePolymorphicBases(nullptr));
    EXPECT_EQ(analyzer->getPrimaryBase(nullptr), nullptr);
    EXPECT_EQ(analyzer->getNonPrimaryBases(nullptr).size(), 0);
    EXPECT_EQ(analyzer->calculateBaseOffset(nullptr, nullptr), 0);
}

// ============================================================================
// Test 12: GetVtblFieldName Static Method
// ============================================================================

TEST_F(MultipleInheritanceAnalyzerTest, GetVtblFieldNameStatic) {
    EXPECT_EQ(MultipleInheritanceAnalyzer::getVtblFieldName(0), "lpVtbl");
    EXPECT_EQ(MultipleInheritanceAnalyzer::getVtblFieldName(1), "lpVtbl2");
    EXPECT_EQ(MultipleInheritanceAnalyzer::getVtblFieldName(2), "lpVtbl3");
    EXPECT_EQ(MultipleInheritanceAnalyzer::getVtblFieldName(3), "lpVtbl4");
    EXPECT_EQ(MultipleInheritanceAnalyzer::getVtblFieldName(10), "lpVtbl11");
}
