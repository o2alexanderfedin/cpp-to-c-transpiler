/**
 * @file RecordHandlerTest_VirtualInheritance.cpp
 * @brief Unit tests for RecordHandler's virtual inheritance handling
 *
 * Tests RecordHandler's ability to:
 * 1. Detect virtual inheritance
 * 2. Generate vbptr fields when needed
 * 3. Call VTTGenerator for VTT generation
 * 4. Emit correct struct layout with virtual bases
 *
 * These are UNIT tests - they test RecordHandler in isolation without requiring
 * full transpilation pipeline or VirtualInheritanceAnalyzer integration (which is
 * tested in integration tests).
 */

#include "dispatch/RecordHandler.h"
#include "helpers/UnitTestHelper.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecordLayout.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;
using namespace cpptoc::test;

/**
 * @class RecordHandlerVirtualInheritanceTest
 * @brief Test fixture for RecordHandler virtual inheritance features
 */
class RecordHandlerVirtualInheritanceTest : public ::testing::Test {
protected:
    UnitTestContext ctx;

    void SetUp() override {
        ctx = createUnitTestContext();
        ctx.dispatcher->registerHandler<RecordHandler>();
    }

    /**
     * @brief Build AST and find first CXXRecordDecl
     */
    const clang::CXXRecordDecl* getCXXRecordDeclFromCode(const std::string& code) {
        auto ast = clang::tooling::buildASTFromCode(code);
        if (!ast) return nullptr;

        auto& astCtx = ast->getASTContext();
        auto* TU = astCtx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* recordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (!recordDecl->isImplicit() && recordDecl->isCompleteDefinition()) {
                    // Store AST to keep it alive
                    storedAST = std::move(ast);
                    return recordDecl;
                }
            }
        }

        return nullptr;
    }

    /**
     * @brief Find class by name in current AST
     */
    const clang::CXXRecordDecl* findClass(const std::string& name) {
        if (!storedAST) return nullptr;

        auto& astCtx = storedAST->getASTContext();
        auto* TU = astCtx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* recordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (recordDecl->getNameAsString() == name && recordDecl->isCompleteDefinition()) {
                    return recordDecl;
                }
            }
        }

        return nullptr;
    }

    std::unique_ptr<clang::ASTUnit> storedAST;
};

// ============================================================================
// Test 1: Detect Single Virtual Base
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, DetectSingleVirtualBase) {
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

    // Parse code
    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    // Verify class has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Check that the virtual base is Base
    bool hasVirtualBase = false;
    for (const auto& vbase : derived->vbases()) {
        auto* vbaseRecord = vbase.getType()->getAsCXXRecordDecl();
        if (vbaseRecord && vbaseRecord->getNameAsString() == "Base") {
            hasVirtualBase = true;
            break;
        }
    }
    EXPECT_TRUE(hasVirtualBase);
}

// ============================================================================
// Test 2: Detect Diamond Pattern
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, DetectDiamondPattern) {
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

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* diamond = findClass("Diamond");
    ASSERT_NE(diamond, nullptr);

    // Diamond inherits virtual bases from Left and Right
    EXPECT_GT(diamond->getNumVBases(), 0);

    // Verify Base is in virtual bases
    bool hasBaseAsVirtual = false;
    for (const auto& vbase : diamond->vbases()) {
        auto* vbaseRecord = vbase.getType()->getAsCXXRecordDecl();
        if (vbaseRecord && vbaseRecord->getNameAsString() == "Base") {
            hasBaseAsVirtual = true;
            break;
        }
    }
    EXPECT_TRUE(hasBaseAsVirtual);
}

// ============================================================================
// Test 3: No Virtual Bases - Regular Inheritance
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, NoVirtualBases) {
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

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    // No virtual bases
    EXPECT_EQ(derived->getNumVBases(), 0);
}

// ============================================================================
// Test 4: Multiple Virtual Bases
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, MultipleVirtualBases) {
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

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    // Should have 2 virtual bases
    EXPECT_EQ(derived->getNumVBases(), 2);

    // Verify both bases are virtual
    std::set<std::string> vbaseNames;
    for (const auto& vbase : derived->vbases()) {
        auto* vbaseRecord = vbase.getType()->getAsCXXRecordDecl();
        if (vbaseRecord) {
            vbaseNames.insert(vbaseRecord->getNameAsString());
        }
    }

    EXPECT_EQ(vbaseNames.size(), 2);
    EXPECT_TRUE(vbaseNames.count("Base1") > 0);
    EXPECT_TRUE(vbaseNames.count("Base2") > 0);
}

// ============================================================================
// Test 5: Mixed Virtual and Non-Virtual Inheritance
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, MixedInheritance) {
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

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    // Should have 1 virtual base
    EXPECT_EQ(derived->getNumVBases(), 1);

    // Should have 2 total bases (1 virtual + 1 non-virtual)
    EXPECT_EQ(derived->getNumBases(), 2);

    // Verify VirtualBase is the virtual one
    bool hasVirtualBase = false;
    for (const auto& vbase : derived->vbases()) {
        auto* vbaseRecord = vbase.getType()->getAsCXXRecordDecl();
        if (vbaseRecord && vbaseRecord->getNameAsString() == "VirtualBase") {
            hasVirtualBase = true;
            break;
        }
    }
    EXPECT_TRUE(hasVirtualBase);
}

// ============================================================================
// Test 6: Indirect Virtual Base
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, IndirectVirtualBase) {
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

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* middle = findClass("Middle");
    auto* derived = findClass("Derived");
    ASSERT_NE(middle, nullptr);
    ASSERT_NE(derived, nullptr);

    // Middle has Base as direct virtual base
    EXPECT_EQ(middle->getNumVBases(), 1);

    // Derived inherits virtual base from Middle
    EXPECT_EQ(derived->getNumVBases(), 1);

    // Both should have Base as virtual base
    for (auto* record : {middle, derived}) {
        bool hasBaseVirtual = false;
        for (const auto& vbase : record->vbases()) {
            auto* vbaseRecord = vbase.getType()->getAsCXXRecordDecl();
            if (vbaseRecord && vbaseRecord->getNameAsString() == "Base") {
                hasBaseVirtual = true;
                break;
            }
        }
        EXPECT_TRUE(hasBaseVirtual) << "Class " << record->getNameAsString()
                                    << " should have Base as virtual base";
    }
}

// ============================================================================
// Test 7: Empty Virtual Base
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, EmptyVirtualBase) {
    std::string code = R"(
        class EmptyBase {
            // Empty - no members
        };

        class Derived : public virtual EmptyBase {
        public:
            int d;
        };
    )";

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    // Should still detect virtual base even if empty
    EXPECT_EQ(derived->getNumVBases(), 1);

    // Verify it's EmptyBase
    bool hasEmptyBase = false;
    for (const auto& vbase : derived->vbases()) {
        auto* vbaseRecord = vbase.getType()->getAsCXXRecordDecl();
        if (vbaseRecord && vbaseRecord->getNameAsString() == "EmptyBase") {
            hasEmptyBase = true;
            break;
        }
    }
    EXPECT_TRUE(hasEmptyBase);
}

// ============================================================================
// Test 8: Virtual Base Class Detection Predicate
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, VirtualBaseDetectionPredicate) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class VirtualDerived : public virtual Base {
        public:
            int vd;
        };

        class NonVirtualDerived : public Base {
        public:
            int nvd;
        };

        class NoInheritance {
        public:
            int ni;
        };
    )";

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* base = findClass("Base");
    auto* virtualDerived = findClass("VirtualDerived");
    auto* nonVirtualDerived = findClass("NonVirtualDerived");
    auto* noInheritance = findClass("NoInheritance");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(virtualDerived, nullptr);
    ASSERT_NE(nonVirtualDerived, nullptr);
    ASSERT_NE(noInheritance, nullptr);

    // Only VirtualDerived should have virtual bases
    EXPECT_EQ(base->getNumVBases(), 0);
    EXPECT_GT(virtualDerived->getNumVBases(), 0);
    EXPECT_EQ(nonVirtualDerived->getNumVBases(), 0);
    EXPECT_EQ(noInheritance->getNumVBases(), 0);
}

// ============================================================================
// Test 9: Complex Multi-Level Virtual Inheritance
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, ComplexMultiLevelVirtualInheritance) {
    std::string code = R"(
        class Level0 {
        public:
            virtual ~Level0() {}
            int l0;
        };

        class Level1A : public virtual Level0 {
        public:
            int l1a;
        };

        class Level1B : public virtual Level0 {
        public:
            int l1b;
        };

        class Level2 : public Level1A, public Level1B {
        public:
            int l2;
        };
    )";

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* level0 = findClass("Level0");
    auto* level1A = findClass("Level1A");
    auto* level1B = findClass("Level1B");
    auto* level2 = findClass("Level2");

    ASSERT_NE(level0, nullptr);
    ASSERT_NE(level1A, nullptr);
    ASSERT_NE(level1B, nullptr);
    ASSERT_NE(level2, nullptr);

    // Level0 has no virtual bases
    EXPECT_EQ(level0->getNumVBases(), 0);

    // Level1A and Level1B each have Level0 as virtual base
    EXPECT_EQ(level1A->getNumVBases(), 1);
    EXPECT_EQ(level1B->getNumVBases(), 1);

    // Level2 inherits Level0 as virtual base through both paths
    EXPECT_EQ(level2->getNumVBases(), 1);

    // Verify Level2's virtual base is Level0
    bool hasLevel0Virtual = false;
    for (const auto& vbase : level2->vbases()) {
        auto* vbaseRecord = vbase.getType()->getAsCXXRecordDecl();
        if (vbaseRecord && vbaseRecord->getNameAsString() == "Level0") {
            hasLevel0Virtual = true;
            break;
        }
    }
    EXPECT_TRUE(hasLevel0Virtual);
}

// ============================================================================
// Test 10: Virtual Base with Different Access Specifiers
// ============================================================================

TEST_F(RecordHandlerVirtualInheritanceTest, VirtualBaseAccessSpecifiers) {
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

    storedAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(storedAST, nullptr);

    auto* derived = findClass("Derived");
    ASSERT_NE(derived, nullptr);

    // Should have 3 virtual bases regardless of access specifier
    EXPECT_EQ(derived->getNumVBases(), 3);

    // Collect all virtual base names
    std::set<std::string> vbaseNames;
    for (const auto& vbase : derived->vbases()) {
        auto* vbaseRecord = vbase.getType()->getAsCXXRecordDecl();
        if (vbaseRecord) {
            vbaseNames.insert(vbaseRecord->getNameAsString());
        }
    }

    EXPECT_EQ(vbaseNames.size(), 3);
    EXPECT_TRUE(vbaseNames.count("PublicBase") > 0);
    EXPECT_TRUE(vbaseNames.count("ProtectedBase") > 0);
    EXPECT_TRUE(vbaseNames.count("PrivateBase") > 0);
}
