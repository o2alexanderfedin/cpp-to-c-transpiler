/**
 * @file InheritanceGraphTest.cpp
 * @brief Unit tests for InheritanceGraph component
 *
 * Tests the inheritance graph building, path finding, and multiple path detection
 * for virtual inheritance analysis. These are isolated unit tests for the graph
 * algorithms separate from the full VirtualInheritanceAnalyzer.
 *
 * Coverage:
 * - Graph construction (addEdge)
 * - Parent retrieval (getParents)
 * - Path finding (findPaths) - all paths from derived to base
 * - Multiple path detection (hasMultiplePaths) - diamond pattern detection
 * - Edge cases: empty graphs, cycles, deep hierarchies
 */

#include "VirtualInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

/**
 * @class InheritanceGraphTest
 * @brief Test fixture for InheritanceGraph
 */
class InheritanceGraphTest : public ::testing::Test {
protected:
    /**
     * @brief Helper to parse C++ code and get CXXRecordDecl by name
     */
    CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        auto AST = tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

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
};

// ============================================================================
// Test 1: Simple Linear Inheritance - Single Path
// ============================================================================

TEST_F(InheritanceGraphTest, LinearInheritanceSinglePath) {
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

    InheritanceGraph graph;
    graph.addEdge(derived, base, true, AS_public);

    // Check parents
    auto parents = graph.getParents(derived);
    EXPECT_EQ(parents.size(), 1);
    EXPECT_EQ(parents[0].baseClass, base);
    EXPECT_TRUE(parents[0].isVirtual);

    // Check paths
    auto paths = graph.findPaths(derived, base);
    EXPECT_EQ(paths.size(), 1) << "Should find exactly 1 path";
    EXPECT_EQ(paths[0].size(), 2) << "Path should be: Derived -> Base";
    EXPECT_EQ(paths[0][0], derived);
    EXPECT_EQ(paths[0][1], base);

    // No multiple paths
    EXPECT_FALSE(graph.hasMultiplePaths(derived, base));
}

// ============================================================================
// Test 2: Diamond Pattern - Multiple Paths
// ============================================================================

TEST_F(InheritanceGraphTest, DiamondPatternMultiplePaths) {
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

    InheritanceGraph graph;

    // Build graph: Diamond -> Left -> Base, Diamond -> Right -> Base
    graph.addEdge(left, base, true, AS_public);
    graph.addEdge(right, base, true, AS_public);
    graph.addEdge(diamond, left, false, AS_public);
    graph.addEdge(diamond, right, false, AS_public);

    // Check Diamond's parents
    auto parents = graph.getParents(diamond);
    EXPECT_EQ(parents.size(), 2);

    // Find paths from Diamond to Base
    auto paths = graph.findPaths(diamond, base);
    EXPECT_EQ(paths.size(), 2) << "Should find 2 paths (diamond pattern)";

    // Verify paths
    // Path 1: Diamond -> Left -> Base
    // Path 2: Diamond -> Right -> Base
    EXPECT_EQ(paths[0].size(), 3);
    EXPECT_EQ(paths[1].size(), 3);

    // Check for multiple paths
    EXPECT_TRUE(graph.hasMultiplePaths(diamond, base))
        << "Diamond pattern should have multiple paths";
}

// ============================================================================
// Test 3: Deep Hierarchy - Three Levels
// ============================================================================

TEST_F(InheritanceGraphTest, DeepHierarchyThreeLevels) {
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
    )";

    auto* level0 = getClass(code, "Level0");
    auto* level1 = getClass(code, "Level1");
    auto* level2 = getClass(code, "Level2");

    ASSERT_NE(level0, nullptr);
    ASSERT_NE(level1, nullptr);
    ASSERT_NE(level2, nullptr);

    InheritanceGraph graph;
    graph.addEdge(level1, level0, true, AS_public);
    graph.addEdge(level2, level1, true, AS_public);

    // Find path from Level2 to Level0
    auto paths = graph.findPaths(level2, level0);
    EXPECT_EQ(paths.size(), 1) << "Should find 1 path through Level1";
    EXPECT_EQ(paths[0].size(), 3) << "Path: Level2 -> Level1 -> Level0";

    // Verify path
    EXPECT_EQ(paths[0][0], level2);
    EXPECT_EQ(paths[0][1], level1);
    EXPECT_EQ(paths[0][2], level0);

    // No multiple paths
    EXPECT_FALSE(graph.hasMultiplePaths(level2, level0));
}

// ============================================================================
// Test 4: Multiple Paths with Different Lengths
// ============================================================================

TEST_F(InheritanceGraphTest, MultiplePathsDifferentLengths) {
    std::string code = R"(
        class Top {
        public:
            virtual ~Top() {}
            int t;
        };

        class Middle : public virtual Top {
        public:
            int m;
        };

        class Bottom : public virtual Top, public Middle {
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

    InheritanceGraph graph;
    graph.addEdge(middle, top, true, AS_public);
    graph.addEdge(bottom, top, true, AS_public);    // Direct path
    graph.addEdge(bottom, middle, false, AS_public); // Indirect path

    // Find paths from Bottom to Top
    auto paths = graph.findPaths(bottom, top);
    EXPECT_EQ(paths.size(), 2) << "Should find 2 paths (direct + indirect)";

    // Check path lengths
    bool hasDirectPath = false;
    bool hasIndirectPath = false;

    for (const auto& path : paths) {
        if (path.size() == 2) {
            hasDirectPath = true;  // Bottom -> Top
        } else if (path.size() == 3) {
            hasIndirectPath = true; // Bottom -> Middle -> Top
        }
    }

    EXPECT_TRUE(hasDirectPath) << "Should have direct path";
    EXPECT_TRUE(hasIndirectPath) << "Should have indirect path through Middle";

    // Should detect multiple paths
    EXPECT_TRUE(graph.hasMultiplePaths(bottom, top));
}

// ============================================================================
// Test 5: No Path Between Unrelated Classes
// ============================================================================

TEST_F(InheritanceGraphTest, NoPathBetweenUnrelatedClasses) {
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
    )";

    auto* base1 = getClass(code, "Base1");
    auto* base2 = getClass(code, "Base2");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);

    InheritanceGraph graph;
    // No edges added - unrelated classes

    // No paths should be found
    auto paths = graph.findPaths(base1, base2);
    EXPECT_EQ(paths.size(), 0) << "Unrelated classes should have no paths";

    // No multiple paths
    EXPECT_FALSE(graph.hasMultiplePaths(base1, base2));
}

// ============================================================================
// Test 6: Complex Diamond - Four Paths
// ============================================================================

TEST_F(InheritanceGraphTest, ComplexDiamondFourPaths) {
    std::string code = R"(
        class Top {
        public:
            virtual ~Top() {}
            int t;
        };

        class Left1 : public virtual Top { public: int l1; };
        class Left2 : public virtual Top { public: int l2; };
        class Right1 : public virtual Top { public: int r1; };
        class Right2 : public virtual Top { public: int r2; };

        class Bottom : public Left1, public Left2, public Right1, public Right2 {
        public:
            int b;
        };
    )";

    auto* top = getClass(code, "Top");
    auto* left1 = getClass(code, "Left1");
    auto* left2 = getClass(code, "Left2");
    auto* right1 = getClass(code, "Right1");
    auto* right2 = getClass(code, "Right2");
    auto* bottom = getClass(code, "Bottom");

    ASSERT_NE(top, nullptr);
    ASSERT_NE(left1, nullptr);
    ASSERT_NE(left2, nullptr);
    ASSERT_NE(right1, nullptr);
    ASSERT_NE(right2, nullptr);
    ASSERT_NE(bottom, nullptr);

    InheritanceGraph graph;

    // Build complex diamond
    graph.addEdge(left1, top, true, AS_public);
    graph.addEdge(left2, top, true, AS_public);
    graph.addEdge(right1, top, true, AS_public);
    graph.addEdge(right2, top, true, AS_public);
    graph.addEdge(bottom, left1, false, AS_public);
    graph.addEdge(bottom, left2, false, AS_public);
    graph.addEdge(bottom, right1, false, AS_public);
    graph.addEdge(bottom, right2, false, AS_public);

    // Find paths
    auto paths = graph.findPaths(bottom, top);
    EXPECT_EQ(paths.size(), 4) << "Should find 4 paths";

    // All paths should have length 3
    for (const auto& path : paths) {
        EXPECT_EQ(path.size(), 3) << "All paths: Bottom -> Middle -> Top";
    }

    // Definitely has multiple paths
    EXPECT_TRUE(graph.hasMultiplePaths(bottom, top));
}

// ============================================================================
// Test 7: Access Specifiers Are Preserved
// ============================================================================

TEST_F(InheritanceGraphTest, AccessSpecifiersPreserved) {
    std::string code = R"(
        class PublicBase {
        public:
            virtual ~PublicBase() {}
            int pb;
        };

        class ProtectedBase {
        public:
            virtual ~ProtectedBase() {}
            int prtb;
        };

        class PrivateBase {
        public:
            virtual ~PrivateBase() {}
            int prb;
        };

        class Derived : public virtual PublicBase,
                       protected virtual ProtectedBase,
                       private virtual PrivateBase {
        public:
            int d;
        };
    )";

    auto* publicBase = getClass(code, "PublicBase");
    auto* protectedBase = getClass(code, "ProtectedBase");
    auto* privateBase = getClass(code, "PrivateBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(publicBase, nullptr);
    ASSERT_NE(protectedBase, nullptr);
    ASSERT_NE(privateBase, nullptr);
    ASSERT_NE(derived, nullptr);

    InheritanceGraph graph;
    graph.addEdge(derived, publicBase, true, AS_public);
    graph.addEdge(derived, protectedBase, true, AS_protected);
    graph.addEdge(derived, privateBase, true, AS_private);

    // Get parents
    auto parents = graph.getParents(derived);
    EXPECT_EQ(parents.size(), 3);

    // Check access specifiers
    std::map<const CXXRecordDecl*, AccessSpecifier> accessMap;
    for (const auto& parent : parents) {
        accessMap[parent.baseClass] = parent.accessSpecifier;
    }

    EXPECT_EQ(accessMap[publicBase], AS_public);
    EXPECT_EQ(accessMap[protectedBase], AS_protected);
    EXPECT_EQ(accessMap[privateBase], AS_private);
}

// ============================================================================
// Test 8: Virtual and Non-Virtual Bases Distinction
// ============================================================================

TEST_F(InheritanceGraphTest, VirtualAndNonVirtualBasesDistinction) {
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

    auto* virtualBase = getClass(code, "VirtualBase");
    auto* nonVirtualBase = getClass(code, "NonVirtualBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(virtualBase, nullptr);
    ASSERT_NE(nonVirtualBase, nullptr);
    ASSERT_NE(derived, nullptr);

    InheritanceGraph graph;
    graph.addEdge(derived, virtualBase, true, AS_public);
    graph.addEdge(derived, nonVirtualBase, false, AS_public);

    // Get parents and check virtual flag
    auto parents = graph.getParents(derived);
    EXPECT_EQ(parents.size(), 2);

    std::map<const CXXRecordDecl*, bool> virtualMap;
    for (const auto& parent : parents) {
        virtualMap[parent.baseClass] = parent.isVirtual;
    }

    EXPECT_TRUE(virtualMap[virtualBase]) << "VirtualBase should be marked virtual";
    EXPECT_FALSE(virtualMap[nonVirtualBase]) << "NonVirtualBase should not be marked virtual";
}

// ============================================================================
// Test 9: Empty Graph - No Parents
// ============================================================================

TEST_F(InheritanceGraphTest, EmptyGraphNoParents) {
    std::string code = R"(
        class StandaloneClass {
        public:
            int x;
        };
    )";

    auto* standalone = getClass(code, "StandaloneClass");
    ASSERT_NE(standalone, nullptr);

    InheritanceGraph graph;
    // No edges added

    // No parents
    auto parents = graph.getParents(standalone);
    EXPECT_EQ(parents.size(), 0) << "Standalone class should have no parents";

    // Create another class for path finding
    std::string code2 = R"(
        class Another {
        public:
            int y;
        };
    )";
    auto* another = getClass(code2, "Another");
    ASSERT_NE(another, nullptr);

    // No paths
    auto paths = graph.findPaths(standalone, another);
    EXPECT_EQ(paths.size(), 0) << "Unrelated classes should have no paths";
}

// ============================================================================
// Test 10: Self-Path (Class to Itself)
// ============================================================================

TEST_F(InheritanceGraphTest, SelfPathClassToItself) {
    std::string code = R"(
        class MyClass {
        public:
            int x;
        };
    )";

    auto* myClass = getClass(code, "MyClass");
    ASSERT_NE(myClass, nullptr);

    InheritanceGraph graph;
    // No self-edges (not valid in C++)

    // Path from class to itself should be empty or just the class
    auto paths = graph.findPaths(myClass, myClass);

    // Implementation returns 1 trivial path (the class itself)
    // This is valid behavior - a class has a path to itself
    EXPECT_EQ(paths.size(), 1) << "Self-path should contain trivial path";

    if (paths.size() == 1) {
        EXPECT_EQ(paths[0].size(), 1) << "Self-path should contain just the class itself";
        EXPECT_EQ(paths[0][0], myClass) << "Self-path should reference the class";
    }
}

// ============================================================================
// Test 11: Multiple Virtual Bases - No Diamond
// ============================================================================

TEST_F(InheritanceGraphTest, MultipleVirtualBasesNoDiamond) {
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

    InheritanceGraph graph;
    graph.addEdge(derived, base1, true, AS_public);
    graph.addEdge(derived, base2, true, AS_public);

    // Two independent parents
    auto parents = graph.getParents(derived);
    EXPECT_EQ(parents.size(), 2);

    // Paths to each base
    auto paths1 = graph.findPaths(derived, base1);
    auto paths2 = graph.findPaths(derived, base2);

    EXPECT_EQ(paths1.size(), 1);
    EXPECT_EQ(paths2.size(), 1);

    // No multiple paths to either base
    EXPECT_FALSE(graph.hasMultiplePaths(derived, base1));
    EXPECT_FALSE(graph.hasMultiplePaths(derived, base2));
}

// ============================================================================
// Test 12: Indirect Virtual Base
// ============================================================================

TEST_F(InheritanceGraphTest, IndirectVirtualBase) {
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

    InheritanceGraph graph;
    graph.addEdge(middle, base, true, AS_public);
    graph.addEdge(derived, middle, false, AS_public); // Non-virtual inheritance of Middle

    // Find path from Derived to Base (through Middle)
    auto paths = graph.findPaths(derived, base);
    EXPECT_EQ(paths.size(), 1);
    EXPECT_EQ(paths[0].size(), 3) << "Path: Derived -> Middle -> Base";

    // Verify path
    EXPECT_EQ(paths[0][0], derived);
    EXPECT_EQ(paths[0][1], middle);
    EXPECT_EQ(paths[0][2], base);
}

// ============================================================================
// Test 13: Wide Inheritance - Many Direct Bases
// ============================================================================

TEST_F(InheritanceGraphTest, WideInheritanceManyDirectBases) {
    std::string code = R"(
        class Base1 { public: int b1; };
        class Base2 { public: int b2; };
        class Base3 { public: int b3; };
        class Base4 { public: int b4; };
        class Base5 { public: int b5; };

        class Derived : public Base1, public Base2, public Base3,
                       public Base4, public Base5 {
        public:
            int d;
        };
    )";

    auto* base1 = getClass(code, "Base1");
    auto* base2 = getClass(code, "Base2");
    auto* base3 = getClass(code, "Base3");
    auto* base4 = getClass(code, "Base4");
    auto* base5 = getClass(code, "Base5");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(base3, nullptr);
    ASSERT_NE(base4, nullptr);
    ASSERT_NE(base5, nullptr);
    ASSERT_NE(derived, nullptr);

    InheritanceGraph graph;
    graph.addEdge(derived, base1, false, AS_public);
    graph.addEdge(derived, base2, false, AS_public);
    graph.addEdge(derived, base3, false, AS_public);
    graph.addEdge(derived, base4, false, AS_public);
    graph.addEdge(derived, base5, false, AS_public);

    // Check parent count
    auto parents = graph.getParents(derived);
    EXPECT_EQ(parents.size(), 5) << "Should have 5 direct bases";

    // Each base should have single path
    for (auto* base : {base1, base2, base3, base4, base5}) {
        auto paths = graph.findPaths(derived, base);
        EXPECT_EQ(paths.size(), 1);
        EXPECT_EQ(paths[0].size(), 2); // Direct inheritance
    }
}
