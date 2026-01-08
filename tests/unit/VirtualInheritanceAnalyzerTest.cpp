/**
 * @file VirtualInheritanceAnalyzerTest.cpp
 * @brief Comprehensive unit tests for VirtualInheritanceAnalyzer
 *
 * Tests all public methods and edge cases for virtual inheritance analysis.
 * Follows the same patterns as MultipleInheritanceAnalyzerTest.cpp
 */

#include "VirtualInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

/**
 * @class VirtualInheritanceAnalyzerTest
 * @brief Test fixture for VirtualInheritanceAnalyzer
 */
class VirtualInheritanceAnalyzerTest : public ::testing::Test {
protected:
    /**
     * @brief Helper to parse C++ code and get CXXRecordDecl by name
     */
    CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        auto AST = tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

        analyzer = std::make_unique<VirtualInheritanceAnalyzer>();
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

    /**
     * @brief Analyze all classes in current context
     */
    void analyzeAllClasses() {
        for (auto* decl : context->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = dyn_cast<CXXRecordDecl>(decl)) {
                if (record->isCompleteDefinition()) {
                    analyzer->analyzeClass(record);
                }
            }
        }
    }

    std::unique_ptr<clang::ASTUnit> context;
    std::unique_ptr<VirtualInheritanceAnalyzer> analyzer;
};

// ============================================================================
// Test 1: Detect Single Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, DetectSingleVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* derived = getClass(code, "Derived");
    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Base has no virtual bases
    EXPECT_FALSE(analyzer->hasVirtualBases(base));
    EXPECT_EQ(analyzer->getVirtualBases(base).size(), 0);

    // Derived has Base as virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));
    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 1);
    EXPECT_EQ(vbases[0]->getNameAsString(), "Base");

    // Derived needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 2: Detect Diamond Pattern
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, DetectDiamondPattern) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Left : public virtual Base {
        public:
            int l;
        };

        class Right : public virtual Base {
        public:
            int r;
        };

        class Diamond : public Left, public Right {
        public:
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* left = getClass(code, "Left");
    auto* right = getClass(code, "Right");
    auto* diamond = getClass(code, "Diamond");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(left, nullptr);
    ASSERT_NE(right, nullptr);
    ASSERT_NE(diamond, nullptr);

    analyzeAllClasses();

    // Diamond should be detected as diamond pattern
    EXPECT_TRUE(analyzer->isDiamondPattern(diamond));

    // Diamond has Base as virtual base (inherited from Left and Right)
    EXPECT_TRUE(analyzer->hasVirtualBases(diamond));
    auto vbases = analyzer->getVirtualBases(diamond);
    EXPECT_EQ(vbases.size(), 1);
    EXPECT_EQ(vbases[0]->getNameAsString(), "Base");

    // Diamond needs VTT
    EXPECT_TRUE(analyzer->needsVTT(diamond));
}

// ============================================================================
// Test 3: Ignore Non-Virtual Inheritance
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, IgnoreNonVirtualInheritance) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Derived : public Base {
        public:
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* derived = getClass(code, "Derived");
    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Neither should have virtual bases
    EXPECT_FALSE(analyzer->hasVirtualBases(base));
    EXPECT_FALSE(analyzer->hasVirtualBases(derived));

    // Neither needs VTT
    EXPECT_FALSE(analyzer->needsVTT(base));
    EXPECT_FALSE(analyzer->needsVTT(derived));

    // Not diamond pattern
    EXPECT_FALSE(analyzer->isDiamondPattern(derived));
}

// ============================================================================
// Test 4: Multiple Virtual Bases (No Diamond)
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, MultipleVirtualBasesNoDiamond) {
    std::string code = R"(
        class Base1 {
        public:
            virtual ~Base1() {}
            int b1;
        };

        class Base2 {
        public:
            virtual ~Base2() {}
            int b2;
        };

        class Derived : public virtual Base1, public virtual Base2 {
        public:
            int d;
        };
    )";

    auto* base1 = getClass(code, "Base1");
    auto* base2 = getClass(code, "Base2");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Derived has two virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));
    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 2);

    // Not a diamond pattern (no shared base)
    EXPECT_FALSE(analyzer->isDiamondPattern(derived));

    // Still needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 5: Indirect Virtual Bases
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, IndirectVirtualBases) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Middle : public virtual Base {
        public:
            int m;
        };

        class Derived : public Middle {
        public:
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* middle = getClass(code, "Middle");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(middle, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Middle has Base as direct virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(middle));
    auto middleVBases = analyzer->getVirtualBases(middle);
    EXPECT_EQ(middleVBases.size(), 1);
    EXPECT_EQ(middleVBases[0]->getNameAsString(), "Base");

    // Derived inherits virtual base from Middle
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));
    auto derivedVBases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(derivedVBases.size(), 1);
    EXPECT_EQ(derivedVBases[0]->getNameAsString(), "Base");

    // Both need VTT
    EXPECT_TRUE(analyzer->needsVTT(middle));
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 6: Mixed Virtual and Non-Virtual Inheritance
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, MixedVirtualAndNonVirtualInheritance) {
    std::string code = R"(
        class VirtualBase {
        public:
            virtual ~VirtualBase() {}
            int vb;
        };

        class NonVirtualBase {
        public:
            virtual ~NonVirtualBase() {}
            int nvb;
        };

        class Derived : public virtual VirtualBase, public NonVirtualBase {
        public:
            int d;
        };
    )";

    auto* vbase = getClass(code, "VirtualBase");
    auto* nvbase = getClass(code, "NonVirtualBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(vbase, nullptr);
    ASSERT_NE(nvbase, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Derived should have only VirtualBase as virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));
    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 1);
    EXPECT_EQ(vbases[0]->getNameAsString(), "VirtualBase");

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 7: Empty Virtual Base Class
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, EmptyVirtualBaseClass) {
    std::string code = R"(
        class EmptyBase {
            // Empty class with no members
        };

        class Derived : public virtual EmptyBase {
        public:
            int d;
        };
    )";

    auto* emptyBase = getClass(code, "EmptyBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(emptyBase, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Derived should still detect virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));
    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 1);
    EXPECT_EQ(vbases[0]->getNameAsString(), "EmptyBase");

    // Needs VTT even for empty base
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 8: Deep Inheritance Hierarchy
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, DeepInheritanceHierarchy) {
    std::string code = R"(
        class Level0 {
        public:
            virtual ~Level0() {}
            int l0;
        };

        class Level1 : public virtual Level0 {
        public:
            int l1;
        };

        class Level2 : public virtual Level1 {
        public:
            int l2;
        };

        class Level3 : public virtual Level2 {
        public:
            int l3;
        };
    )";

    auto* level0 = getClass(code, "Level0");
    auto* level1 = getClass(code, "Level1");
    auto* level2 = getClass(code, "Level2");
    auto* level3 = getClass(code, "Level3");

    ASSERT_NE(level0, nullptr);
    ASSERT_NE(level1, nullptr);
    ASSERT_NE(level2, nullptr);
    ASSERT_NE(level3, nullptr);

    analyzeAllClasses();

    // Each level should have virtual bases
    EXPECT_FALSE(analyzer->hasVirtualBases(level0));
    EXPECT_TRUE(analyzer->hasVirtualBases(level1));
    EXPECT_TRUE(analyzer->hasVirtualBases(level2));
    EXPECT_TRUE(analyzer->hasVirtualBases(level3));

    // Level3 should have all levels as virtual bases
    auto level3VBases = analyzer->getVirtualBases(level3);
    EXPECT_GE(level3VBases.size(), 1); // At least Level2 is virtual

    // All levels with virtual bases need VTT
    EXPECT_TRUE(analyzer->needsVTT(level1));
    EXPECT_TRUE(analyzer->needsVTT(level2));
    EXPECT_TRUE(analyzer->needsVTT(level3));
}

// ============================================================================
// Test 9: Complex Diamond Pattern
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, ComplexDiamondPattern) {
    std::string code = R"(
        class Top {
        public:
            virtual ~Top() {}
            int t;
        };

        class Left1 : public virtual Top {
        public:
            int l1;
        };

        class Left2 : public virtual Top {
        public:
            int l2;
        };

        class Right1 : public virtual Top {
        public:
            int r1;
        };

        class Right2 : public virtual Top {
        public:
            int r2;
        };

        class Bottom : public Left1, public Left2, public Right1, public Right2 {
        public:
            int b;
        };
    )";

    auto* top = getClass(code, "Top");
    auto* bottom = getClass(code, "Bottom");

    ASSERT_NE(top, nullptr);
    ASSERT_NE(bottom, nullptr);

    analyzeAllClasses();

    // Bottom should be diamond pattern
    EXPECT_TRUE(analyzer->isDiamondPattern(bottom));

    // Bottom should have Top as virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(bottom));
    auto vbases = analyzer->getVirtualBases(bottom);
    EXPECT_GE(vbases.size(), 1);

    // Check that Top appears in virtual bases
    bool hasTop = false;
    for (auto* vbase : vbases) {
        if (vbase->getNameAsString() == "Top") {
            hasTop = true;
            break;
        }
    }
    EXPECT_TRUE(hasTop);

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(bottom));
}

// ============================================================================
// Test 10: Virtual Base Construction Order
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, VirtualBaseConstructionOrder) {
    std::string code = R"(
        class Base1 {
        public:
            virtual ~Base1() {}
            int b1;
        };

        class Base2 {
        public:
            virtual ~Base2() {}
            int b2;
        };

        class Middle : public virtual Base1, public virtual Base2 {
        public:
            int m;
        };

        class Derived : public Middle {
        public:
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Get virtual base construction order
    auto constructionOrder = analyzer->getVirtualBaseConstructionOrder(derived);

    // Should have at least Base1 and Base2 in construction order
    EXPECT_GE(constructionOrder.size(), 2);

    // Verify all are valid classes
    for (auto* vbase : constructionOrder) {
        EXPECT_NE(vbase, nullptr);
    }
}

// ============================================================================
// Test 11: Most Derived Analysis
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, MostDerivedAnalysis) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* derived = getClass(code, "Derived");
    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // When constructing Derived, Derived is most-derived
    EXPECT_TRUE(analyzer->isMostDerived(derived, derived));

    // When constructing Base as part of Derived, Base is not most-derived
    EXPECT_FALSE(analyzer->isMostDerived(base, derived));

    // When constructing Base standalone, Base is most-derived
    EXPECT_TRUE(analyzer->isMostDerived(base, base));
}

// ============================================================================
// Test 12: Inheritance Graph Paths
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, InheritanceGraphPaths) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Left : public virtual Base {
        public:
            int l;
        };

        class Right : public virtual Base {
        public:
            int r;
        };

        class Diamond : public Left, public Right {
        public:
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* diamond = getClass(code, "Diamond");
    ASSERT_NE(base, nullptr);
    ASSERT_NE(diamond, nullptr);

    analyzeAllClasses();

    // Get inheritance graph
    const auto& graph = analyzer->getInheritanceGraph();

    // There should be multiple paths from Diamond to Base
    EXPECT_TRUE(graph.hasMultiplePaths(diamond, base));

    // Get all paths
    auto paths = graph.findPaths(diamond, base);
    EXPECT_GE(paths.size(), 2); // At least through Left and Right
}

// ============================================================================
// Test 13: No Virtual Bases, No VTT
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, NoVirtualBasesNoVTT) {
    std::string code = R"(
        class SimpleClass {
        public:
            int value;
        };
    )";

    auto* simple = getClass(code, "SimpleClass");
    ASSERT_NE(simple, nullptr);

    analyzeAllClasses();

    // No virtual bases
    EXPECT_FALSE(analyzer->hasVirtualBases(simple));

    // No VTT needed
    EXPECT_FALSE(analyzer->needsVTT(simple));

    // Not diamond pattern
    EXPECT_FALSE(analyzer->isDiamondPattern(simple));
}

// ============================================================================
// Test 14: Virtual Base with Polymorphic Base
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, VirtualBaseWithPolymorphicBase) {
    std::string code = R"(
        class Polymorphic {
        public:
            virtual void foo() = 0;
        };

        class VirtualBase : public virtual Polymorphic {
        public:
            void foo() override {}
            int vb;
        };

        class Derived : public VirtualBase {
        public:
            int d;
        };
    )";

    auto* polymorphic = getClass(code, "Polymorphic");
    auto* vbase = getClass(code, "VirtualBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(polymorphic, nullptr);
    ASSERT_NE(vbase, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // VirtualBase has Polymorphic as virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(vbase));

    // Derived inherits virtual base from VirtualBase
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    // Both need VTT
    EXPECT_TRUE(analyzer->needsVTT(vbase));
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 15: Repeated Diamond Pattern
// ============================================================================

TEST_F(VirtualInheritanceAnalyzerTest, RepeatedDiamondPattern) {
    std::string code = R"(
        class Top {
        public:
            virtual ~Top() {}
            int t;
        };

        class LeftTop : public virtual Top {
        public:
            int lt;
        };

        class RightTop : public virtual Top {
        public:
            int rt;
        };

        class Middle : public LeftTop, public RightTop {
        public:
            int m;
        };

        class LeftBottom : public Middle {
        public:
            int lb;
        };

        class RightBottom : public Middle {
        public:
            int rb;
        };

        class Bottom : public LeftBottom, public RightBottom {
        public:
            int b;
        };
    )";

    auto* top = getClass(code, "Top");
    auto* middle = getClass(code, "Middle");
    auto* bottom = getClass(code, "Bottom");

    ASSERT_NE(top, nullptr);
    ASSERT_NE(middle, nullptr);
    ASSERT_NE(bottom, nullptr);

    analyzeAllClasses();

    // Middle is diamond pattern
    EXPECT_TRUE(analyzer->isDiamondPattern(middle));

    // Bottom has complex virtual inheritance
    EXPECT_TRUE(analyzer->hasVirtualBases(bottom));

    // All need VTT
    EXPECT_TRUE(analyzer->needsVTT(middle));
    EXPECT_TRUE(analyzer->needsVTT(bottom));
}
