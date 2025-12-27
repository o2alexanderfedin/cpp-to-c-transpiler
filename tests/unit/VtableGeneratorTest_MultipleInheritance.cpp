/**
 * @file VtableGeneratorTest_MultipleInheritance.cpp
 * @brief TDD tests for VtableGenerator multiple inheritance support (Phase 46 Group 1 Task 2)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (10-12 tests):
 * 1. GenerateVtableForPrimaryBase - Generate vtable struct for primary base
 * 2. GenerateVtableForNonPrimaryBase - Generate vtable struct for non-primary base
 * 3. MultipleVtablesForMultipleBases - Multiple vtables for multiple bases
 * 4. VtableNamingConventionCorrect - Pattern: ClassName_BaseName_vtable
 * 5. EachVtableHasCorrectMethods - Each vtable contains methods from that base
 * 6. OverrideMethodsInCorrectVtables - Override methods appear in correct vtables
 * 7. EmptyBaseVtable - Pure virtual base vtable
 * 8. DeepHierarchyVtables - Deep hierarchy vtable generation
 * 9. MethodSignatureCompatibility - Method signatures match base interface
 * 10. PrimaryBaseCompatibility - Primary base can use ClassName_vtable (backward compatible)
 * 11. ThreeBaseVtables - Three bases generate three vtables
 * 12. MixedVirtualNonVirtualBases - Only polymorphic bases get vtables
 *
 * Multiple Inheritance Vtable Pattern:
 * C++: class Shape : public IDrawable, public ISerializable { ... };
 * C:   struct Shape_IDrawable_vtable { ... };
 *      struct Shape_ISerializable_vtable { ... };
 */

#include "VtableGenerator.h"
#include "VirtualMethodAnalyzer.h"
#include "OverrideResolver.h"
#include "MultipleInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

/**
 * @class VtableGeneratorMultipleInheritanceTest
 * @brief Test fixture for VtableGenerator multiple inheritance support
 */
class VtableGeneratorMultipleInheritanceTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> AST;
    std::unique_ptr<VirtualMethodAnalyzer> analyzer;
    std::unique_ptr<OverrideResolver> resolver;
    std::unique_ptr<VtableGenerator> generator;
    std::unique_ptr<MultipleInheritanceAnalyzer> miAnalyzer;

    void SetUp() override {
        // Will be initialized per test
    }

    /**
     * @brief Helper to parse C++ code and initialize analyzers
     */
    bool buildAST(const std::string& code) {
        AST = tooling::buildASTFromCode(code);
        if (!AST) return false;

        analyzer = std::make_unique<VirtualMethodAnalyzer>(AST->getASTContext());
        resolver = std::make_unique<OverrideResolver>(AST->getASTContext(), *analyzer);
        generator = std::make_unique<VtableGenerator>(AST->getASTContext(), *analyzer, resolver.get());
        miAnalyzer = std::make_unique<MultipleInheritanceAnalyzer>(AST->getASTContext());
        return true;
    }

    /**
     * @brief Helper to find a class by name
     */
    CXXRecordDecl* findClass(const std::string& name) {
        if (!AST) return nullptr;

        auto* TU = AST->getASTContext().getTranslationUnitDecl();
        for (auto* decl : TU->decls()) {
            if (auto* record = dyn_cast<CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == name && record->isCompleteDefinition()) {
                    return record;
                }
            }
        }
        return nullptr;
    }
};

// ============================================================================
// Test 1: Generate Vtable for Primary Base
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, GenerateVtableForPrimaryBase) {
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

    ASSERT_TRUE(buildAST(code));
    auto* shape = findClass("Shape");
    ASSERT_NE(shape, nullptr);

    // Generate vtable for primary base (IDrawable)
    auto bases = miAnalyzer->analyzePolymorphicBases(shape);
    ASSERT_EQ(bases.size(), 2);
    ASSERT_TRUE(bases[0].IsPrimary);

    std::string vtableCode = generator->generateVtableForBase(shape, bases[0].BaseDecl);

    // Verify vtable struct name (primary base pattern)
    EXPECT_NE(vtableCode.find("struct Shape_IDrawable_vtable"), std::string::npos)
        << "Expected 'struct Shape_IDrawable_vtable' in output";

    // Verify draw method in vtable
    EXPECT_NE(vtableCode.find("draw"), std::string::npos)
        << "Expected 'draw' method in primary base vtable";
}

// ============================================================================
// Test 2: Generate Vtable for Non-Primary Base
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, GenerateVtableForNonPrimaryBase) {
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

    ASSERT_TRUE(buildAST(code));
    auto* shape = findClass("Shape");
    ASSERT_NE(shape, nullptr);

    // Generate vtable for non-primary base (ISerializable)
    auto bases = miAnalyzer->analyzePolymorphicBases(shape);
    ASSERT_EQ(bases.size(), 2);
    ASSERT_FALSE(bases[1].IsPrimary);

    std::string vtableCode = generator->generateVtableForBase(shape, bases[1].BaseDecl);

    // Verify vtable struct name
    EXPECT_NE(vtableCode.find("struct Shape_ISerializable_vtable"), std::string::npos)
        << "Expected 'struct Shape_ISerializable_vtable' in output";

    // Verify serialize method in vtable
    EXPECT_NE(vtableCode.find("serialize"), std::string::npos)
        << "Expected 'serialize' method in non-primary base vtable";
}

// ============================================================================
// Test 3: Multiple Vtables for Multiple Bases
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, MultipleVtablesForMultipleBases) {
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

    ASSERT_TRUE(buildAST(code));
    auto* shape = findClass("Shape");
    ASSERT_NE(shape, nullptr);

    // Generate all vtables
    std::string allVtables = generator->generateAllVtablesForMultipleInheritance(shape);

    // Verify both vtable structs present
    EXPECT_NE(allVtables.find("struct Shape_IDrawable_vtable"), std::string::npos)
        << "Expected primary base vtable";
    EXPECT_NE(allVtables.find("struct Shape_ISerializable_vtable"), std::string::npos)
        << "Expected non-primary base vtable";

    // Verify both methods present in appropriate vtables
    EXPECT_NE(allVtables.find("draw"), std::string::npos);
    EXPECT_NE(allVtables.find("serialize"), std::string::npos);
}

// ============================================================================
// Test 4: Vtable Naming Convention Correct
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, VtableNamingConventionCorrect) {
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
        public:
            void method1() override {}
            void method2() override {}
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    std::string allVtables = generator->generateAllVtablesForMultipleInheritance(derived);

    // Pattern: ClassName_BaseName_vtable
    EXPECT_NE(allVtables.find("struct Derived_Base1_vtable"), std::string::npos)
        << "Expected pattern: Derived_Base1_vtable";
    EXPECT_NE(allVtables.find("struct Derived_Base2_vtable"), std::string::npos)
        << "Expected pattern: Derived_Base2_vtable";
}

// ============================================================================
// Test 5: Each Vtable Has Correct Methods
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, EachVtableHasCorrectMethods) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
            virtual void render() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
            virtual void deserialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
        public:
            void draw() override {}
            void render() override {}
            void serialize() override {}
            void deserialize() override {}
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* shape = findClass("Shape");
    ASSERT_NE(shape, nullptr);

    auto bases = miAnalyzer->analyzePolymorphicBases(shape);
    ASSERT_EQ(bases.size(), 2);

    // Generate IDrawable vtable
    std::string drawableVtable = generator->generateVtableForBase(shape, bases[0].BaseDecl);
    EXPECT_NE(drawableVtable.find("draw"), std::string::npos);
    EXPECT_NE(drawableVtable.find("render"), std::string::npos);

    // Generate ISerializable vtable
    std::string serializableVtable = generator->generateVtableForBase(shape, bases[1].BaseDecl);
    EXPECT_NE(serializableVtable.find("serialize"), std::string::npos);
    EXPECT_NE(serializableVtable.find("deserialize"), std::string::npos);
}

// ============================================================================
// Test 6: Override Methods in Correct Vtables
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, OverrideMethodsInCorrectVtables) {
    std::string code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Derived : public Base1, public Base2 {
        public:
            void foo() override {}  // Override Base1::foo
            void bar() override {}  // Override Base2::bar
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    auto bases = miAnalyzer->analyzePolymorphicBases(derived);
    ASSERT_EQ(bases.size(), 2);

    // Base1 vtable should have foo
    std::string base1Vtable = generator->generateVtableForBase(derived, bases[0].BaseDecl);
    EXPECT_NE(base1Vtable.find("foo"), std::string::npos);
    EXPECT_EQ(base1Vtable.find("bar"), std::string::npos) << "bar should not be in Base1 vtable";

    // Base2 vtable should have bar
    std::string base2Vtable = generator->generateVtableForBase(derived, bases[1].BaseDecl);
    EXPECT_NE(base2Vtable.find("bar"), std::string::npos);
    EXPECT_EQ(base2Vtable.find("foo"), std::string::npos) << "foo should not be in Base2 vtable";
}

// ============================================================================
// Test 7: Empty Base Vtable (Pure Virtual)
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, EmptyBaseVtable) {
    std::string code = R"(
        class IInterface {
        public:
            virtual void method() = 0;
        };

        class IOther {
        public:
            virtual void other() = 0;
        };

        class Impl : public IInterface, public IOther {
        public:
            void method() override {}
            void other() override {}
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* impl = findClass("Impl");
    ASSERT_NE(impl, nullptr);

    auto bases = miAnalyzer->analyzePolymorphicBases(impl);
    ASSERT_EQ(bases.size(), 2);

    // Both bases are pure virtual interfaces
    std::string vtable1 = generator->generateVtableForBase(impl, bases[0].BaseDecl);
    std::string vtable2 = generator->generateVtableForBase(impl, bases[1].BaseDecl);

    EXPECT_FALSE(vtable1.empty());
    EXPECT_FALSE(vtable2.empty());
}

// ============================================================================
// Test 8: Deep Hierarchy Vtables
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, DeepHierarchyVtables) {
    std::string code = R"(
        class IBase1 {
        public:
            virtual void base1Method() = 0;
        };

        class IBase2 {
        public:
            virtual void base2Method() = 0;
        };

        class Intermediate1 : public IBase1 {
        public:
            void base1Method() override {}
            virtual void inter1Method() {}
        };

        class Intermediate2 : public IBase2 {
        public:
            void base2Method() override {}
            virtual void inter2Method() {}
        };

        class Derived : public Intermediate1, public Intermediate2 {
        public:
            void inter1Method() override {}
            void inter2Method() override {}
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    // Should generate vtables for immediate bases
    std::string allVtables = generator->generateAllVtablesForMultipleInheritance(derived);
    EXPECT_FALSE(allVtables.empty());
}

// ============================================================================
// Test 9: Method Signature Compatibility
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, MethodSignatureCompatibility) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual int draw(int x, int y) = 0;
        };

        class ISerializable {
        public:
            virtual void serialize(const char* filename) = 0;
        };

        class Shape : public IDrawable, public ISerializable {
        public:
            int draw(int x, int y) override { return 0; }
            void serialize(const char* filename) override {}
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* shape = findClass("Shape");
    ASSERT_NE(shape, nullptr);

    auto bases = miAnalyzer->analyzePolymorphicBases(shape);
    ASSERT_EQ(bases.size(), 2);

    // Verify IDrawable vtable has correct signature
    std::string drawableVtable = generator->generateVtableForBase(shape, bases[0].BaseDecl);
    EXPECT_NE(drawableVtable.find("int"), std::string::npos) << "draw returns int";
    EXPECT_NE(drawableVtable.find("draw"), std::string::npos);

    // Verify ISerializable vtable has correct signature
    std::string serializableVtable = generator->generateVtableForBase(shape, bases[1].BaseDecl);
    EXPECT_NE(serializableVtable.find("void"), std::string::npos);
    EXPECT_NE(serializableVtable.find("serialize"), std::string::npos);
}

// ============================================================================
// Test 10: Three Base Vtables
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, ThreeBaseVtables) {
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
        public:
            void draw() override {}
            void serialize() override {}
            void onClick() override {}
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* widget = findClass("Widget");
    ASSERT_NE(widget, nullptr);

    std::string allVtables = generator->generateAllVtablesForMultipleInheritance(widget);

    // Verify all three vtables present
    EXPECT_NE(allVtables.find("struct Widget_IDrawable_vtable"), std::string::npos);
    EXPECT_NE(allVtables.find("struct Widget_ISerializable_vtable"), std::string::npos);
    EXPECT_NE(allVtables.find("struct Widget_IClickable_vtable"), std::string::npos);
}

// ============================================================================
// Test 11: Mixed Virtual Non-Virtual Bases
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, MixedVirtualNonVirtualBases) {
    std::string code = R"(
        class NonVirtual {
        public:
            int x;
        };

        class IVirtual {
        public:
            virtual void method() = 0;
        };

        class Derived : public NonVirtual, public IVirtual {
        public:
            void method() override {}
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    auto bases = miAnalyzer->analyzePolymorphicBases(derived);

    // Only IVirtual should be in the list
    EXPECT_EQ(bases.size(), 1);
    EXPECT_EQ(bases[0].BaseDecl->getNameAsString(), "IVirtual");

    std::string allVtables = generator->generateAllVtablesForMultipleInheritance(derived);

    // Should only have Derived_vtable (single polymorphic inheritance)
    // Pattern: Derived_vtable (since only one polymorphic base)
    EXPECT_NE(allVtables.find("Derived_vtable"), std::string::npos)
        << "Should have Derived_vtable for single polymorphic inheritance";
    EXPECT_EQ(allVtables.find("NonVirtual_vtable"), std::string::npos)
        << "NonVirtual base should not have vtable";
}

// ============================================================================
// Test 12: Backward Compatibility - Single Inheritance Still Works
// ============================================================================

TEST_F(VtableGeneratorMultipleInheritanceTest, BackwardCompatibilitySingleInheritance) {
    std::string code = R"(
        class Base {
        public:
            virtual void method() {}
        };

        class Derived : public Base {
        public:
            void method() override {}
        };
    )";

    ASSERT_TRUE(buildAST(code));
    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    // For single inheritance, should still use generateVtableStruct
    std::string vtable = generator->generateVtableStruct(derived);
    EXPECT_NE(vtable.find("struct Derived_vtable"), std::string::npos);
    EXPECT_NE(vtable.find("method"), std::string::npos);
}
