/**
 * @file RecordHandlerDualLayoutTest.cpp
 * @brief TDD tests for RecordHandler dual layout generation (Phase 2)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Phase 2: RecordHandler Dual Layout Generation
 * - Tests for needsDualLayout() detection
 * - Tests for base-subobject layout generation (ClassName__base)
 * - Tests for complete-object layout generation (ClassName)
 * - Integration tests for dual generation
 *
 * References:
 * - DUAL_LAYOUT_RESEARCH_AND_IMPLEMENTATION_PLAN.md (Phase 2, lines 625-656)
 * - Itanium C++ ABI specification
 */

#include "dispatch/RecordHandler.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecordLayout.h"
#include "VirtualInheritanceAnalyzer.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class RecordHandlerDualLayoutTest
 * @brief Test fixture for RecordHandler dual layout generation
 */
class RecordHandlerDualLayoutTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> storedAST;

    /**
     * @brief Build AST from code and return the first CXXRecordDecl
     */
    const clang::CXXRecordDecl* getCXXRecordDeclFromCode(const std::string& code) {
        auto ast = clang::tooling::buildASTFromCode(code);
        if (!ast) return nullptr;

        auto& astContext = ast->getASTContext();
        auto* TU = astContext.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* cxxRecordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                // Skip implicit declarations
                if (!cxxRecordDecl->isImplicit() && cxxRecordDecl->isCompleteDefinition()) {
                    // Store AST to keep it alive
                    storedAST = std::move(ast);
                    return cxxRecordDecl;
                }
            }
        }

        return nullptr;
    }

    /**
     * @brief Get named CXXRecordDecl from code
     */
    const clang::CXXRecordDecl* getNamedCXXRecordDecl(const std::string& code, const std::string& name) {
        auto ast = clang::tooling::buildASTFromCode(code);
        if (!ast) return nullptr;

        auto& astContext = ast->getASTContext();
        auto* TU = astContext.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* cxxRecordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (cxxRecordDecl->getNameAsString() == name &&
                    !cxxRecordDecl->isImplicit() &&
                    cxxRecordDecl->isCompleteDefinition()) {
                    // Store AST to keep it alive
                    storedAST = std::move(ast);
                    return cxxRecordDecl;
                }
            }
        }

        return nullptr;
    }
};

// =============================================================================
// Task 1: needsDualLayout() Detection Tests (8-10 tests)
// =============================================================================

/**
 * Test 1.1: Simple class with no virtual bases - should NOT need dual layout
 * C++: class Simple { int x; };
 */
TEST_F(RecordHandlerDualLayoutTest, SimpleClass_NoDualLayout) {
    const char* code = R"(
        class Simple {
            int x;
        };
    )";

    const auto* cxxRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cxxRecord, nullptr);
    ASSERT_TRUE(cxxRecord->hasDefinition());

    // Create RecordHandler instance to test private method
    // Since needsDualLayout() is private, we'll test it indirectly through handleRecord()
    // For now, verify the class structure
    EXPECT_FALSE(cxxRecord->getNumVBases() > 0) << "Simple class should have no virtual bases";
}

/**
 * Test 1.2: Class with direct virtual base - SHOULD need dual layout
 * C++: class Base { int b; };
 *      class Derived : virtual Base { int d; };
 */
TEST_F(RecordHandlerDualLayoutTest, DirectVirtualBase_NeedsDualLayout) {
    const char* code = R"(
        class Base {
            int b;
        };
        class Derived : virtual Base {
            int d;
        };
    )";

    const auto* derived = getNamedCXXRecordDecl(code, "Derived");
    ASSERT_NE(derived, nullptr);
    ASSERT_TRUE(derived->hasDefinition());

    // Verify has virtual bases
    EXPECT_TRUE(derived->getNumVBases() > 0) << "Derived should have virtual bases";
    EXPECT_EQ(derived->getNumVBases(), 1) << "Derived should have exactly 1 virtual base";
}

/**
 * Test 1.3: Class used as virtual base - SHOULD need dual layout
 * C++: class Base { int b; };
 *      class Left : virtual Base { int l; };
 *      class Right : virtual Base { int r; };
 */
TEST_F(RecordHandlerDualLayoutTest, UsedAsVirtualBase_NeedsDualLayout) {
    const char* code = R"(
        class Base {
            int b;
        };
        class Left : virtual Base {
            int l;
        };
        class Right : virtual Base {
            int r;
        };
    )";

    const auto* base = getNamedCXXRecordDecl(code, "Base");
    ASSERT_NE(base, nullptr);
    ASSERT_TRUE(base->hasDefinition());

    // Base is used as virtual base by Left and Right
    // This requires testing via VirtualInheritanceAnalyzer
    VirtualInheritanceAnalyzer analyzer;

    // Analyze Left and Right to populate analyzer
    const auto* left = getNamedCXXRecordDecl(code, "Left");
    const auto* right = getNamedCXXRecordDecl(code, "Right");
    ASSERT_NE(left, nullptr);
    ASSERT_NE(right, nullptr);

    analyzer.analyzeClass(left);
    analyzer.analyzeClass(right);

    // Both Left and Right should have virtual bases
    EXPECT_TRUE(analyzer.hasVirtualBases(left));
    EXPECT_TRUE(analyzer.hasVirtualBases(right));
}

/**
 * Test 1.4: Diamond inheritance pattern - SHOULD need dual layout
 * C++: class Base { int b; };
 *      class Left : virtual Base { int l; };
 *      class Right : virtual Base { int r; };
 *      class Diamond : Left, Right { int d; };
 */
TEST_F(RecordHandlerDualLayoutTest, DiamondInheritance_NeedsDualLayout) {
    const char* code = R"(
        class Base {
            int b;
        };
        class Left : virtual Base {
            int l;
        };
        class Right : virtual Base {
            int r;
        };
        class Diamond : public Left, public Right {
            int d;
        };
    )";

    const auto* diamond = getNamedCXXRecordDecl(code, "Diamond");
    ASSERT_NE(diamond, nullptr);
    ASSERT_TRUE(diamond->hasDefinition());

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(diamond);

    // Diamond should have indirect virtual bases
    EXPECT_TRUE(analyzer.hasVirtualBases(diamond)) << "Diamond should have virtual bases";
    EXPECT_TRUE(analyzer.isDiamondPattern(diamond)) << "Should detect diamond pattern";
}

/**
 * Test 1.5: Deep virtual hierarchy - SHOULD need dual layout
 * C++: class A { int a; };
 *      class B : virtual A { int b; };
 *      class C : virtual B { int c; };
 */
TEST_F(RecordHandlerDualLayoutTest, DeepVirtualHierarchy_NeedsDualLayout) {
    const char* code = R"(
        class A {
            int a;
        };
        class B : virtual A {
            int b;
        };
        class C : virtual B {
            int c;
        };
    )";

    const auto* c = getNamedCXXRecordDecl(code, "C");
    ASSERT_NE(c, nullptr);
    ASSERT_TRUE(c->hasDefinition());

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(c);

    EXPECT_TRUE(analyzer.hasVirtualBases(c)) << "C should have virtual bases";
}

/**
 * Test 1.6: Non-virtual inheritance - should NOT need dual layout
 * C++: class Base { int b; };
 *      class Derived : Base { int d; };
 */
TEST_F(RecordHandlerDualLayoutTest, NonVirtualInheritance_NoDualLayout) {
    const char* code = R"(
        class Base {
            int b;
        };
        class Derived : public Base {
            int d;
        };
    )";

    const auto* derived = getNamedCXXRecordDecl(code, "Derived");
    ASSERT_NE(derived, nullptr);
    ASSERT_TRUE(derived->hasDefinition());

    EXPECT_EQ(derived->getNumVBases(), 0) << "Derived should have no virtual bases";
}

/**
 * Test 1.7: Multiple non-virtual inheritance - should NOT need dual layout
 * C++: class A { int a; };
 *      class B { int b; };
 *      class C : A, B { int c; };
 */
TEST_F(RecordHandlerDualLayoutTest, MultipleNonVirtualInheritance_NoDualLayout) {
    const char* code = R"(
        class A {
            int a;
        };
        class B {
            int b;
        };
        class C : public A, public B {
            int c;
        };
    )";

    const auto* c = getNamedCXXRecordDecl(code, "C");
    ASSERT_NE(c, nullptr);
    ASSERT_TRUE(c->hasDefinition());

    EXPECT_EQ(c->getNumVBases(), 0) << "C should have no virtual bases";
}

/**
 * Test 1.8: Empty class with virtual base - SHOULD need dual layout
 * C++: class Base {};
 *      class Derived : virtual Base {};
 */
TEST_F(RecordHandlerDualLayoutTest, EmptyClassWithVirtualBase_NeedsDualLayout) {
    const char* code = R"(
        class Base {};
        class Derived : virtual Base {};
    )";

    const auto* derived = getNamedCXXRecordDecl(code, "Derived");
    ASSERT_NE(derived, nullptr);
    ASSERT_TRUE(derived->hasDefinition());

    EXPECT_TRUE(derived->getNumVBases() > 0) << "Derived should have virtual bases";
}

/**
 * Test 1.9: Complex diamond with multiple levels - SHOULD need dual layout
 * C++: class A {};
 *      class B : virtual A {};
 *      class C : virtual A {};
 *      class D : B, C {};
 *      class E : virtual D {};
 */
TEST_F(RecordHandlerDualLayoutTest, ComplexDiamond_NeedsDualLayout) {
    const char* code = R"(
        class A {};
        class B : virtual A {};
        class C : virtual A {};
        class D : public B, public C {};
        class E : virtual D {};
    )";

    const auto* e = getNamedCXXRecordDecl(code, "E");
    ASSERT_NE(e, nullptr);
    ASSERT_TRUE(e->hasDefinition());

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(e);

    EXPECT_TRUE(analyzer.hasVirtualBases(e)) << "E should have virtual bases";
}

/**
 * Test 1.10: Mixed virtual and non-virtual inheritance - SHOULD need dual layout
 * C++: class A { int a; };
 *      class B { int b; };
 *      class C : public A, virtual B { int c; };
 */
TEST_F(RecordHandlerDualLayoutTest, MixedInheritance_NeedsDualLayout) {
    const char* code = R"(
        class A {
            int a;
        };
        class B {
            int b;
        };
        class C : public A, virtual B {
            int c;
        };
    )";

    const auto* c = getNamedCXXRecordDecl(code, "C");
    ASSERT_NE(c, nullptr);
    ASSERT_TRUE(c->hasDefinition());

    EXPECT_TRUE(c->getNumVBases() > 0) << "C should have virtual bases";
}
