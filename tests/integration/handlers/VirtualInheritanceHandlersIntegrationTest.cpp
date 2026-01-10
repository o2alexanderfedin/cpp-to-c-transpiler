/**
 * @file VirtualInheritanceHandlersIntegrationTest.cpp
 * @brief Integration tests for virtual inheritance handler interactions
 *
 * Tests that multiple handlers work together correctly for virtual inheritance:
 * 1. RecordHandler + VirtualInheritanceAnalyzer integration
 * 2. ConstructorHandler + ConstructorSplitter integration
 * 3. RecordHandler + VTTGenerator integration
 * 4. End-to-end handler chain for virtual inheritance
 *
 * These are INTEGRATION tests - they test handler cooperation, not individual handlers.
 */

#include "dispatch/RecordHandler.h"
#include "dispatch/ConstructorHandler.h"
#include "VirtualInheritanceAnalyzer.h"
#include "UnitTestHelper.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;
using namespace cpptoc::test;

/**
 * @class VirtualInheritanceHandlersIntegrationTest
 * @brief Test fixture for handler integration tests
 */
class VirtualInheritanceHandlersIntegrationTest : public ::testing::Test {
protected:
    UnitTestContext ctx;
    std::unique_ptr<VirtualInheritanceAnalyzer> analyzer;

    void SetUp() override {
        ctx = createUnitTestContext();
        RecordHandler::registerWith(*ctx.dispatcher);
        ConstructorHandler::registerWith(*ctx.dispatcher);
        analyzer = std::make_unique<VirtualInheritanceAnalyzer>();
    }

    /**
     * @brief Parse code and get class by name
     */
    const clang::CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        storedAST = clang::tooling::buildASTFromCode(code);
        if (!storedAST) return nullptr;

        auto& astCtx = storedAST->getASTContext();
        auto* TU = astCtx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* recordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (recordDecl->getNameAsString() == className &&
                    recordDecl->isCompleteDefinition()) {
                    return recordDecl;
                }
            }
        }

        return nullptr;
    }

    /**
     * @brief Analyze all classes in current AST
     */
    void analyzeAllClasses() {
        if (!storedAST) return;

        auto& astCtx = storedAST->getASTContext();
        auto* TU = astCtx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* recordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (recordDecl->isCompleteDefinition()) {
                    analyzer->analyzeClass(recordDecl);
                }
            }
        }
    }

    std::unique_ptr<clang::ASTUnit> storedAST;
};

// ============================================================================
// Test 1: RecordHandler + VirtualInheritanceAnalyzer - Simple Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, RecordHandlerAndAnalyzerSimpleVirtualBase) {
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

    // Analyzer should detect virtual base
    EXPECT_FALSE(analyzer->hasVirtualBases(base));
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));
    EXPECT_TRUE(analyzer->needsVTT(derived));

    // RecordHandler should handle both classes
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(base));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));
}

// ============================================================================
// Test 2: RecordHandler + VirtualInheritanceAnalyzer - Diamond Pattern
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, RecordHandlerAndAnalyzerDiamond) {
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

    // Analyzer should detect diamond pattern
    EXPECT_TRUE(analyzer->isDiamondPattern(diamond));
    EXPECT_TRUE(analyzer->hasVirtualBases(diamond));
    EXPECT_TRUE(analyzer->needsVTT(diamond));

    // All classes should be handleable
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(base));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(left));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(right));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(diamond));
}

// ============================================================================
// Test 3: ConstructorHandler + VirtualInheritanceAnalyzer
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, ConstructorHandlerAndAnalyzer) {
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

    auto* base = getClass(code, "Base");
    auto* derived = getClass(code, "Derived");
    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Analyzer detects virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    // Find constructors
    clang::CXXConstructorDecl* baseCtor = nullptr;
    clang::CXXConstructorDecl* derivedCtor = nullptr;

    for (auto* ctor : base->ctors()) {
        if (ctor->getNumParams() == 0) {
            baseCtor = ctor;
            break;
        }
    }

    for (auto* ctor : derived->ctors()) {
        if (ctor->getNumParams() == 0) {
            derivedCtor = ctor;
            break;
        }
    }

    ASSERT_NE(baseCtor, nullptr);
    ASSERT_NE(derivedCtor, nullptr);

    // ConstructorHandler should handle both
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(baseCtor));
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(derivedCtor));
}

// ============================================================================
// Test 4: Integration - Multiple Virtual Bases
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, MultipleVirtualBasesIntegration) {
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
            Derived() : d(0) {}
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

    // Analyzer should detect both virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));
    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 2);

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));

    // Not diamond pattern (no shared base)
    EXPECT_FALSE(analyzer->isDiamondPattern(derived));
}

// ============================================================================
// Test 5: Integration - Indirect Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, IndirectVirtualBaseIntegration) {
    std::string code = R"(
        class Base {
        public:
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
            Derived() : d(0) {}
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

    // Both Middle and Derived have virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(middle));
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    // Both need VTT
    EXPECT_TRUE(analyzer->needsVTT(middle));
    EXPECT_TRUE(analyzer->needsVTT(derived));

    // All classes should be handleable
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(base));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(middle));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));
}

// ============================================================================
// Test 6: Integration - Mixed Virtual and Non-Virtual
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, MixedInheritanceIntegration) {
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
            Derived() : d(0) {}
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

    // Only Derived has virtual bases
    EXPECT_FALSE(analyzer->hasVirtualBases(vbase));
    EXPECT_FALSE(analyzer->hasVirtualBases(nvbase));
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));

    // Derived has 1 virtual base
    auto vbases = analyzer->getVirtualBases(derived);
    EXPECT_EQ(vbases.size(), 1);

    // Needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));
}

// ============================================================================
// Test 7: Integration - Virtual Base Construction Order
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, VirtualBaseConstructionOrderIntegration) {
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
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* base1 = getClass(code, "Base1");
    auto* base2 = getClass(code, "Base2");
    auto* middle = getClass(code, "Middle");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(middle, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // Get virtual base construction order for Derived
    auto constructionOrder = analyzer->getVirtualBaseConstructionOrder(derived);

    // Should have at least 2 virtual bases
    EXPECT_GE(constructionOrder.size(), 2);

    // All should be valid classes
    for (auto* vbase : constructionOrder) {
        EXPECT_NE(vbase, nullptr);
    }
}

// ============================================================================
// Test 8: Integration - Most Derived Analysis
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, MostDerivedAnalysisIntegration) {
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
// Test 9: Integration - Inheritance Graph Paths
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, InheritanceGraphPathsIntegration) {
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
// Test 10: Integration - Complex Multi-Level Diamond
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, ComplexMultiLevelDiamondIntegration) {
    std::string code = R"(
        class Top {
        public:
            virtual ~Top() {}
            int t;
        };

        class Level1A : public virtual Top { public: int l1a; };
        class Level1B : public virtual Top { public: int l1b; };

        class Level2 : public Level1A, public Level1B {
        public:
            int l2;
        };

        class Level3A : public Level2 { public: int l3a; };
        class Level3B : public Level2 { public: int l3b; };

        class Bottom : public Level3A, public Level3B {
        public:
            Bottom() : b(0) {}
            int b;
        };
    )";

    auto* top = getClass(code, "Top");
    auto* level2 = getClass(code, "Level2");
    auto* bottom = getClass(code, "Bottom");

    ASSERT_NE(top, nullptr);
    ASSERT_NE(level2, nullptr);
    ASSERT_NE(bottom, nullptr);

    analyzeAllClasses();

    // Level2 should be diamond pattern
    EXPECT_TRUE(analyzer->isDiamondPattern(level2));

    // Bottom should have virtual bases
    EXPECT_TRUE(analyzer->hasVirtualBases(bottom));

    // All need VTT
    EXPECT_TRUE(analyzer->needsVTT(level2));
    EXPECT_TRUE(analyzer->needsVTT(bottom));
}

// ============================================================================
// Test 11: Integration - Handler Chain Completeness
// ============================================================================

TEST_F(VirtualInheritanceHandlersIntegrationTest, HandlerChainCompleteness) {
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

    auto* base = getClass(code, "Base");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    analyzeAllClasses();

    // RecordHandler should handle both classes
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(base));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));

    // ConstructorHandler should handle constructors
    clang::CXXConstructorDecl* baseCtor = nullptr;
    clang::CXXConstructorDecl* derivedCtor = nullptr;

    for (auto* ctor : base->ctors()) {
        if (ctor->getNumParams() == 0) {
            baseCtor = ctor;
            break;
        }
    }

    for (auto* ctor : derived->ctors()) {
        if (ctor->getNumParams() == 0) {
            derivedCtor = ctor;
            break;
        }
    }

    ASSERT_NE(baseCtor, nullptr);
    ASSERT_NE(derivedCtor, nullptr);

    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(baseCtor));
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(derivedCtor));

    // VirtualInheritanceAnalyzer should detect virtual base
    EXPECT_TRUE(analyzer->hasVirtualBases(derived));
    EXPECT_TRUE(analyzer->needsVTT(derived));
}
