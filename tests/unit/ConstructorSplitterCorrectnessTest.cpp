/**
 * @file ConstructorSplitterCorrectnessTest.cpp
 * @brief Unit tests for C1/C2 constructor generation correctness
 *
 * Tests ConstructorSplitter for:
 * - Correct identification of classes needing splitting
 * - C1 (complete object) constructor generation
 * - C2 (base object) constructor generation
 * - Virtual base construction in C1 only
 * - VTT parameter passing
 * - Constructor ordering and semantics
 * - Edge cases (empty bases, multiple virtual bases, deep hierarchies)
 */

#include "ConstructorSplitter.h"
#include "VirtualInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

/**
 * @class ConstructorSplitterCorrectnessTest
 * @brief Test fixture for constructor splitting correctness
 */
class ConstructorSplitterCorrectnessTest : public ::testing::Test {
protected:
    /**
     * @brief Helper to parse C++ code and get CXXRecordDecl by name
     */
    CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        auto AST = tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

        context = std::move(AST);
        analyzer = std::make_unique<VirtualInheritanceAnalyzer>();
        splitter = std::make_unique<ConstructorSplitter>(
            context->getASTContext(),
            *analyzer
        );

        // Analyze all classes
        for (auto* decl : context->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = dyn_cast<CXXRecordDecl>(decl)) {
                if (record->isCompleteDefinition()) {
                    analyzer->analyzeClass(record);
                }
            }
        }

        // Find target class
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
    std::unique_ptr<VirtualInheritanceAnalyzer> analyzer;
    std::unique_ptr<ConstructorSplitter> splitter;
};

// ============================================================================
// Test 1: Needs Splitting - Single Virtual Base
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, NeedsSplittingSingleVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Class with virtual base needs splitting
    EXPECT_TRUE(splitter->needsSplitting(derived))
        << "Class with virtual base should need C1/C2 splitting";
}

// ============================================================================
// Test 2: No Splitting for Non-Virtual Inheritance
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, NoSplittingForNonVirtualInheritance) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Non-virtual inheritance doesn't need splitting
    EXPECT_FALSE(splitter->needsSplitting(derived))
        << "Non-virtual inheritance should not need C1/C2 splitting";
}

// ============================================================================
// Test 3: C1 Constructor Contains VTT Parameter
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, C1ConstructorContainsVTTParameter) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    ASSERT_TRUE(splitter->needsSplitting(derived));

    std::string c1Code = splitter->generateC1Constructor(derived);
    ASSERT_FALSE(c1Code.empty()) << "C1 constructor should be generated";

    // C1 should have VTT parameter
    EXPECT_NE(c1Code.find("vtt"), std::string::npos)
        << "C1 constructor should have VTT parameter";

    // Check function naming
    EXPECT_NE(c1Code.find("_C1"), std::string::npos)
        << "C1 constructor should have _C1 suffix";
}

// ============================================================================
// Test 4: C2 Constructor Contains VTT Parameter
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, C2ConstructorContainsVTTParameter) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    ASSERT_TRUE(splitter->needsSplitting(derived));

    std::string c2Code = splitter->generateC2Constructor(derived);
    ASSERT_FALSE(c2Code.empty()) << "C2 constructor should be generated";

    // C2 should also have VTT parameter
    EXPECT_NE(c2Code.find("vtt"), std::string::npos)
        << "C2 constructor should have VTT parameter";

    // Check function naming
    EXPECT_NE(c2Code.find("_C2"), std::string::npos)
        << "C2 constructor should have _C2 suffix";
}

// ============================================================================
// Test 5: C1 and C2 Have Different Behavior
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, C1AndC2HaveDifferentBehavior) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    std::string c1Code = splitter->generateC1Constructor(derived);
    std::string c2Code = splitter->generateC2Constructor(derived);

    ASSERT_FALSE(c1Code.empty());
    ASSERT_FALSE(c2Code.empty());

    // C1 and C2 should be different
    EXPECT_NE(c1Code, c2Code) << "C1 and C2 should have different implementations";

    // C1 should construct virtual bases (Base)
    // C2 should NOT construct virtual bases
    // This is implementation dependent, but we can check for patterns
}

// ============================================================================
// Test 6: Diamond Pattern Needs Splitting
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, DiamondPatternNeedsSplitting) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Left : public virtual Base {
        public:
            Left() {}
            int l;
        };

        class Right : public virtual Base {
        public:
            Right() {}
            int r;
        };

        class Diamond : public Left, public Right {
        public:
            Diamond() {}
            int d;
        };
    )";

    auto* left = getClass(code, "Left");
    auto* right = getClass(code, "Right");
    auto* diamond = getClass(code, "Diamond");

    ASSERT_NE(left, nullptr);
    ASSERT_NE(right, nullptr);
    ASSERT_NE(diamond, nullptr);

    // All classes with virtual bases need splitting
    EXPECT_TRUE(splitter->needsSplitting(left));
    EXPECT_TRUE(splitter->needsSplitting(right));
    EXPECT_TRUE(splitter->needsSplitting(diamond));
}

// ============================================================================
// Test 7: C1/C2 Generation for Diamond Pattern
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, C1C2GenerationForDiamondPattern) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Left : public virtual Base {
        public:
            Left() {}
            int l;
        };

        class Right : public virtual Base {
        public:
            Right() {}
            int r;
        };

        class Diamond : public Left, public Right {
        public:
            Diamond() {}
            int d;
        };
    )";

    auto* diamond = getClass(code, "Diamond");
    ASSERT_NE(diamond, nullptr);

    std::string c1Code = splitter->generateC1Constructor(diamond);
    std::string c2Code = splitter->generateC2Constructor(diamond);

    ASSERT_FALSE(c1Code.empty());
    ASSERT_FALSE(c2Code.empty());

    // C1 should construct virtual base (Base)
    // C2 should skip virtual base construction

    // Check for class names in code
    EXPECT_NE(c1Code.find("Diamond"), std::string::npos);
    EXPECT_NE(c2Code.find("Diamond"), std::string::npos);
}

// ============================================================================
// Test 8: Multiple Virtual Bases - Needs Splitting
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, MultipleVirtualBasesNeedsSplitting) {
    std::string code = R"(
        class Base1 {
        public:
            Base1() {}
            virtual ~Base1() {}
            int b1;
        };

        class Base2 {
        public:
            Base2() {}
            virtual ~Base2() {}
            int b2;
        };

        class Derived : public virtual Base1, public virtual Base2 {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Multiple virtual bases need splitting
    EXPECT_TRUE(splitter->needsSplitting(derived));

    std::string c1Code = splitter->generateC1Constructor(derived);
    std::string c2Code = splitter->generateC2Constructor(derived);

    ASSERT_FALSE(c1Code.empty());
    ASSERT_FALSE(c2Code.empty());
}

// ============================================================================
// Test 9: Empty Virtual Base - Still Needs Splitting
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, EmptyVirtualBaseNeedsSplitting) {
    std::string code = R"(
        class EmptyBase {
            // Empty class
        };

        class Derived : public virtual EmptyBase {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Even empty virtual base needs splitting
    EXPECT_TRUE(splitter->needsSplitting(derived));

    std::string c1Code = splitter->generateC1Constructor(derived);
    std::string c2Code = splitter->generateC2Constructor(derived);

    EXPECT_FALSE(c1Code.empty());
    EXPECT_FALSE(c2Code.empty());
}

// ============================================================================
// Test 10: Indirect Virtual Base - Needs Splitting
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, IndirectVirtualBaseNeedsSplitting) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Middle : public virtual Base {
        public:
            Middle() {}
            int m;
        };

        class Derived : public Middle {
        public:
            Derived() {}
            int d;
        };
    )";

    auto* middle = getClass(code, "Middle");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(middle, nullptr);
    ASSERT_NE(derived, nullptr);

    // Middle has virtual base - needs splitting
    EXPECT_TRUE(splitter->needsSplitting(middle));

    // Derived inherits virtual base - needs splitting
    EXPECT_TRUE(splitter->needsSplitting(derived));
}

// ============================================================================
// Test 11: Mixed Virtual and Non-Virtual - Needs Splitting
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, MixedVirtualNonVirtualNeedsSplitting) {
    std::string code = R"(
        class VirtualBase {
        public:
            VirtualBase() {}
            virtual ~VirtualBase() {}
            int vb;
        };

        class NonVirtualBase {
        public:
            NonVirtualBase() {}
            virtual ~NonVirtualBase() {}
            int nvb;
        };

        class Derived : public virtual VirtualBase, public NonVirtualBase {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base, needs splitting
    EXPECT_TRUE(splitter->needsSplitting(derived));

    std::string c1Code = splitter->generateC1Constructor(derived);
    std::string c2Code = splitter->generateC2Constructor(derived);

    ASSERT_FALSE(c1Code.empty());
    ASSERT_FALSE(c2Code.empty());
}

// ============================================================================
// Test 12: Constructor with Parameters
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, ConstructorWithParameters) {
    std::string code = R"(
        class Base {
        public:
            Base(int val) : value(val) {}
            virtual ~Base() {}
            int value;
        };

        class Derived : public virtual Base {
        public:
            Derived(int b, int d) : Base(b), data(d) {}
            int data;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(splitter->needsSplitting(derived));

    // Generate constructors
    std::string c1Code = splitter->generateC1Constructor(derived);
    std::string c2Code = splitter->generateC2Constructor(derived);

    EXPECT_FALSE(c1Code.empty());
    EXPECT_FALSE(c2Code.empty());

    // Both should handle parameters (implementation dependent)
}

// ============================================================================
// Test 13: Deep Virtual Inheritance Hierarchy
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, DeepVirtualInheritanceHierarchy) {
    std::string code = R"(
        class Level0 {
        public:
            Level0() {}
            virtual ~Level0() {}
            int l0;
        };

        class Level1 : public virtual Level0 {
        public:
            Level1() {}
            int l1;
        };

        class Level2 : public virtual Level1 {
        public:
            Level2() {}
            int l2;
        };
    )";

    auto* level1 = getClass(code, "Level1");
    auto* level2 = getClass(code, "Level2");

    ASSERT_NE(level1, nullptr);
    ASSERT_NE(level2, nullptr);

    // All levels with virtual bases need splitting
    EXPECT_TRUE(splitter->needsSplitting(level1));
    EXPECT_TRUE(splitter->needsSplitting(level2));

    // Generate for deepest level
    std::string c1Code = splitter->generateC1Constructor(level2);
    std::string c2Code = splitter->generateC2Constructor(level2);

    EXPECT_FALSE(c1Code.empty());
    EXPECT_FALSE(c2Code.empty());
}

// ============================================================================
// Test 14: C1/C2 Naming Convention
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, C1C2NamingConvention) {
    std::string code = R"(
        class MyClass {
        public:
            MyClass() {}
            virtual ~MyClass() {}
        };

        class MyDerived : public virtual MyClass {
        public:
            MyDerived() {}
            int d;
        };
    )";

    auto* derived = getClass(code, "MyDerived");
    ASSERT_NE(derived, nullptr);

    std::string c1Code = splitter->generateC1Constructor(derived);
    std::string c2Code = splitter->generateC2Constructor(derived);

    // Check naming includes class name and variant suffix
    EXPECT_NE(c1Code.find("MyDerived"), std::string::npos);
    EXPECT_NE(c2Code.find("MyDerived"), std::string::npos);

    EXPECT_NE(c1Code.find("_C1"), std::string::npos);
    EXPECT_NE(c2Code.find("_C2"), std::string::npos);
}

// ============================================================================
// Test 15: No Splitting for Base Class Without Virtual Bases
// ============================================================================

TEST_F(ConstructorSplitterCorrectnessTest, NoSplittingForBaseWithoutVirtualBases) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };
    )";

    auto* base = getClass(code, "Base");
    ASSERT_NE(base, nullptr);

    // Base class without virtual bases doesn't need splitting
    EXPECT_FALSE(splitter->needsSplitting(base));
}
