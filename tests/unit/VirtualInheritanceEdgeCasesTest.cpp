/**
 * @file VirtualInheritanceEdgeCasesTest.cpp
 * @brief Unit tests for virtual inheritance edge cases
 *
 * Tests edge cases and corner scenarios for virtual inheritance:
 * - Empty virtual base classes (EBO - Empty Base Optimization)
 * - Deep inheritance hierarchies (10+ levels)
 * - Wide inheritance (many virtual bases)
 * - Multiple paths to same virtual base (complex diamonds)
 * - Mix of virtual and non-virtual inheritance
 * - Virtual base construction ordering
 * - Most-derived class detection
 * - Circular dependency patterns (if possible)
 */

#include "VirtualInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

/**
 * @class VirtualInheritanceEdgeCasesTest
 * @brief Test fixture for virtual inheritance edge cases
 */
class VirtualInheritanceEdgeCasesTest : public ::testing::Test {
protected:
    /**
     * @brief Helper to parse C++ code and get CXXRecordDecl by name
     */
    CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        // Only rebuild AST if code has changed
        if (code != lastCode || !context) {
            auto AST = tooling::buildASTFromCode(code);
            if (!AST) return nullptr;

            context = std::move(AST);
            analyzer = std::make_unique<VirtualInheritanceAnalyzer>();
            lastCode = code;

            // Analyze all classes
            for (auto* decl : context->getASTContext().getTranslationUnitDecl()->decls()) {
                if (auto* record = dyn_cast<CXXRecordDecl>(decl)) {
                    if (record->isCompleteDefinition()) {
                        analyzer->analyzeClass(record);
                    }
                }
            }
        }

        // Find target class
        for (auto* decl : context->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = dyn_cast<CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == className && record->isCompleteDefinition()) {
                    return record->getCanonicalDecl();
                }
            }
        }
        return nullptr;
    }

    std::string lastCode;
    std::unique_ptr<clang::ASTUnit> context;
    std::unique_ptr<VirtualInheritanceAnalyzer> analyzer;
};

// ============================================================================
// Test 1: Empty Base Optimization (EBO) Candidate
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, EmptyBaseOptimizationCandidate) {
    std::string code = R"(
        // Empty base class - candidate for EBO
        class EmptyBase {
            // No members, no virtual functions
        };

        class Derived : public virtual EmptyBase {
        public:
            int data;
        };
    )";

    auto* emptyBase = getClass(code, "EmptyBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(emptyBase, nullptr);
    ASSERT_NE(derived, nullptr);

    // Empty base is still a virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 1);
    EXPECT_EQ(vbases[0], emptyBase);

    // Even empty virtual base needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 2: Deep Inheritance Hierarchy (10 Levels)
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, DeepInheritanceHierarchy10Levels) {
    std::string code = R"(
        class L0 { public: virtual ~L0() {} int l0; };
        class L1 : public virtual L0 { public: int l1; };
        class L2 : public virtual L1 { public: int l2; };
        class L3 : public virtual L2 { public: int l3; };
        class L4 : public virtual L3 { public: int l4; };
        class L5 : public virtual L4 { public: int l5; };
        class L6 : public virtual L5 { public: int l6; };
        class L7 : public virtual L6 { public: int l7; };
        class L8 : public virtual L7 { public: int l8; };
        class L9 : public virtual L8 { public: int l9; };
    )";

    auto* l0 = getClass(code, "L0");
    auto* l5 = getClass(code, "L5");
    auto* l9 = getClass(code, "L9");

    ASSERT_NE(l0, nullptr);
    ASSERT_NE(l5, nullptr);
    ASSERT_NE(l9, nullptr);

    // L0 has no virtual bases
    EXPECT_FALSE(analyzer->hasVirtualBases(l0));

    // All other levels have virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(l5));
    EXPECT_TRUE(analyzer->hasVirtualBases(l9));

    // Deep hierarchy should work correctly
    auto vbases = analyzer->getVirtualBases(l9);
    EXPECT_GT(vbases.size(), 0);

    // L9 needs VTT
    EXPECT_TRUE(analyzer->needsVTT(l9));
}

// ============================================================================
// Test 3: Wide Inheritance (10 Virtual Bases)
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, WideInheritance10VirtualBases) {
    std::string code = R"(
        class B0 { public: virtual ~B0() {} int b0; };
        class B1 { public: virtual ~B1() {} int b1; };
        class B2 { public: virtual ~B2() {} int b2; };
        class B3 { public: virtual ~B3() {} int b3; };
        class B4 { public: virtual ~B4() {} int b4; };
        class B5 { public: virtual ~B5() {} int b5; };
        class B6 { public: virtual ~B6() {} int b6; };
        class B7 { public: virtual ~B7() {} int b7; };
        class B8 { public: virtual ~B8() {} int b8; };
        class B9 { public: virtual ~B9() {} int b9; };

        class Wide : public virtual B0, public virtual B1, public virtual B2,
                     public virtual B3, public virtual B4, public virtual B5,
                     public virtual B6, public virtual B7, public virtual B8,
                     public virtual B9 {
        public:
            int w;
        };
    )";

    auto* wide = getClass(code, "Wide");
    ASSERT_NE(wide, nullptr);

    // Should have 10 virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(wide));

    auto vbases = analyzer->getVirtualBases(wide);
    EXPECT_EQ(vbases.size(), 10) << "Should have 10 virtual bases";

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(wide));
}

// ============================================================================
// Test 4: Complex Diamond - Multiple Paths Through Different Routes
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, ComplexDiamondMultiplePaths) {
    std::string code = R"(
        class Top {
        public:
            virtual ~Top() {}
            int t;
        };

        // Two paths from Top to Bottom through different intermediate classes
        class Path1A : public virtual Top { public: int p1a; };
        class Path1B : public virtual Path1A { public: int p1b; };

        class Path2A : public virtual Top { public: int p2a; };
        class Path2B : public virtual Path2A { public: int p2b; };

        class Bottom : public Path1B, public Path2B {
        public:
            int b;
        };
    )";

    auto* top = getClass(code, "Top");
    auto* bottom = getClass(code, "Bottom");

    ASSERT_NE(top, nullptr);
    ASSERT_NE(bottom, nullptr);

    // Bottom should have virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(bottom));

    // Should detect diamond pattern
    EXPECT_TRUE(analyzer->isDiamondPattern(bottom));

    // Get virtual bases (should include Top and intermediate classes)
    auto vbases = analyzer->getVirtualBases(bottom);
    EXPECT_GT(vbases.size(), 0);

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(bottom));
}

// ============================================================================
// Test 5: Repeated Diamond Pattern
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, RepeatedDiamondPattern) {
    std::string code = R"(
        class A {
        public:
            virtual ~A() {}
            int a;
        };

        class B : public virtual A { public: int b; };
        class C : public virtual A { public: int c; };
        class D : public B, public C { public: int d; };  // First diamond

        class E : public virtual D { public: int e; };
        class F : public virtual D { public: int f; };
        class G : public E, public F { public: int g; };  // Second diamond
    )";

    auto* a = getClass(code, "A");
    auto* d = getClass(code, "D");
    auto* g = getClass(code, "G");

    ASSERT_NE(a, nullptr);
    ASSERT_NE(d, nullptr);
    ASSERT_NE(g, nullptr);

    // D forms first diamond
    EXPECT_TRUE(analyzer->isDiamondPattern(d));

    // G has virtual base D
    EXPECT_TRUE(analyzer->hasVirtualBases(g));

    // G forms second diamond with D as virtual base
    EXPECT_TRUE(analyzer->needsVTT(g));
}

// ============================================================================
// Test 6: Virtual Base with Non-Virtual Methods
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, VirtualBaseWithNonVirtualMethods) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            // Non-virtual destructor
            ~Base() {}
            // Non-virtual methods
            void method1() {}
            int method2(int x) { return x * 2; }
            int data;
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

    // Virtual inheritance even without virtual functions
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 1);
    EXPECT_EQ(vbases[0], base);

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 7: Virtual Base Construction Ordering
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, VirtualBaseConstructionOrdering) {
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

    // Get construction order for virtual bases
    auto order = analyzer->getVirtualBaseConstructionOrder(diamond);

    // Should have Base in the construction order
    EXPECT_GT(order.size(), 0);

    // Base should appear (virtual base must be constructed first)
    bool hasBase = false;
    for (const auto* vbase : order) {
        if (vbase == base) {
            hasBase = true;
            break;
        }
    }
    EXPECT_TRUE(hasBase) << "Construction order should include virtual base";
}

// ============================================================================
// Test 8: Most-Derived Class Detection
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, MostDerivedClassDetection) {
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

    // Derived is most-derived when constructing Derived
    EXPECT_TRUE(analyzer->isMostDerived(derived, derived));

    // Middle is NOT most-derived when constructing Derived
    EXPECT_FALSE(analyzer->isMostDerived(middle, derived));

    // Middle IS most-derived when constructing Middle
    EXPECT_TRUE(analyzer->isMostDerived(middle, middle));
}

// ============================================================================
// Test 9: Mix of Virtual and Non-Virtual to Same Base
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, MixVirtualNonVirtualSameBase) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class VirtualPath : public virtual Base {
        public:
            int vp;
        };

        class NonVirtualPath : public Base {
        public:
            int nvp;
        };

        class Derived : public VirtualPath, public NonVirtualPath {
        public:
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    // Derived has virtual base through VirtualPath
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    // Should still need VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 10: Empty Virtual Base in Diamond
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, EmptyVirtualBaseInDiamond) {
    std::string code = R"(
        // Empty base
        class EmptyTop {
            // No members
        };

        class Left : public virtual EmptyTop {
        public:
            int l;
        };

        class Right : public virtual EmptyTop {
        public:
            int r;
        };

        class Diamond : public Left, public Right {
        public:
            int d;
        };
    )";

    auto* emptyTop = getClass(code, "EmptyTop");
    auto* diamond = getClass(code, "Diamond");

    ASSERT_NE(emptyTop, nullptr);
    ASSERT_NE(diamond, nullptr);

    // Diamond pattern with empty base
    EXPECT_TRUE(analyzer->isDiamondPattern(diamond));

    // Has virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(diamond));

    // Needs VTT even with empty base
    EXPECT_TRUE(analyzer->needsVTT(diamond));
}

// ============================================================================
// Test 11: Virtual Base with Only Static Members
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, VirtualBaseWithOnlyStaticMembers) {
    std::string code = R"(
        class StaticBase {
        public:
            static int counter;
            static void increment() { counter++; }
        };

        class Derived : public virtual StaticBase {
        public:
            int d;
        };
    )";

    auto* staticBase = getClass(code, "StaticBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(staticBase, nullptr);
    ASSERT_NE(derived, nullptr);

    // Virtual inheritance with static-only base
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 1);

    // Still needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 12: Virtual Inheritance with Templates (Instantiated)
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, VirtualInheritanceWithTemplatesInstantiated) {
    std::string code = R"(
        template<typename T>
        class TemplateBase {
        public:
            virtual ~TemplateBase() {}
            T value;
        };

        class Derived : public virtual TemplateBase<int> {
        public:
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Virtual inheritance of template instantiation
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 13: Multiple Inheritance Paths with Different Access Specifiers
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, MultiplePathsDifferentAccessSpecifiers) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class PublicPath : public virtual Base {
        public:
            int pp;
        };

        class ProtectedPath : protected virtual Base {
        public:
            int prtp;
        };

        class PrivatePath : private virtual Base {
        public:
            int prp;
        };

        class Derived : public PublicPath, public ProtectedPath, public PrivatePath {
        public:
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Should have virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    // Should detect diamond (multiple paths to Base)
    EXPECT_TRUE(analyzer->isDiamondPattern(derived));

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 14: Virtual Base with Pure Virtual Methods
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, VirtualBaseWithPureVirtualMethods) {
    std::string code = R"(
        class AbstractBase {
        public:
            virtual ~AbstractBase() {}
            virtual void pureMethod() = 0;
            int b;
        };

        class Derived : public virtual AbstractBase {
        public:
            virtual void pureMethod() override {}
            int d;
        };
    )";

    auto* abstractBase = getClass(code, "AbstractBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(abstractBase, nullptr);
    ASSERT_NE(derived, nullptr);

    // Virtual inheritance of abstract base
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 1);
    EXPECT_EQ(vbases[0], abstractBase);

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 15: Extremely Complex Hierarchy
// ============================================================================

TEST_F(VirtualInheritanceEdgeCasesTest, ExtremelyComplexHierarchy) {
    std::string code = R"(
        class Root { public: virtual ~Root() {} int r; };

        class A1 : public virtual Root { public: int a1; };
        class A2 : public virtual Root { public: int a2; };
        class B1 : public virtual A1 { public: int b1; };
        class B2 : public virtual A1 { public: int b2; };
        class B3 : public virtual A2 { public: int b3; };
        class B4 : public virtual A2 { public: int b4; };

        class C1 : public B1, public B2 { public: int c1; };
        class C2 : public B3, public B4 { public: int c2; };

        class Final : public C1, public C2 { public: int f; };
    )";

    auto* root = getClass(code, "Root");
    auto* finalClass = getClass(code, "Final");

    ASSERT_NE(root, nullptr);
    ASSERT_NE(finalClass, nullptr);

    // Final has virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(finalClass));

    // Complex diamond pattern
    EXPECT_TRUE(analyzer->isDiamondPattern(finalClass));

    // Get all virtual bases
    auto vbases = analyzer->getVirtualBases(finalClass);
    EXPECT_GT(vbases.size(), 0);

    // Should include Root
    bool hasRoot = false;
    for (const auto* vbase : vbases) {
        if (vbase == root) {
            hasRoot = true;
            break;
        }
    }
    EXPECT_TRUE(hasRoot);

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(finalClass));
}
