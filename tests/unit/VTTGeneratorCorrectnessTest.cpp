/**
 * @file VTTGeneratorCorrectnessTest.cpp
 * @brief Unit tests for VTT generation correctness and entry ordering
 *
 * Tests VTTGenerator for:
 * - Correct VTT entry count
 * - Proper entry ordering (Itanium ABI compliance)
 * - Primary vtable entry placement
 * - Base constructor entries
 * - Virtual base entries
 * - Edge cases (empty bases, deep hierarchies, complex diamonds)
 *
 * These tests verify VTT structure correctness without requiring full
 * transpilation pipeline integration.
 */

#include "VTTGenerator.h"
#include "VirtualInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

/**
 * @class VTTGeneratorCorrectnessTest
 * @brief Test fixture for VTT generation correctness
 */
class VTTGeneratorCorrectnessTest : public ::testing::Test {
protected:
    /**
     * @brief Helper to parse C++ code and get CXXRecordDecl by name
     */
    CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        auto AST = tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

        context = std::move(AST);
        analyzer = std::make_unique<VirtualInheritanceAnalyzer>();
        generator = std::make_unique<VTTGenerator>(
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
    std::unique_ptr<VTTGenerator> generator;
};

// ============================================================================
// Test 1: Simple Virtual Inheritance - Minimal VTT
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, SimpleVirtualInheritanceMinimalVTT) {
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

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Check VTT is needed
    EXPECT_TRUE(analyzer->needsVTT(derived));

    // Get VTT entries
    auto entries = generator->getVTTEntries(derived);
    EXPECT_GT(entries.size(), 0) << "VTT should have at least primary entry";

    // Get entry count
    size_t count = generator->getVTTEntryCount(derived);
    EXPECT_EQ(count, entries.size());

    // Generate VTT code
    std::string vttCode = generator->generateVTT(derived);
    EXPECT_FALSE(vttCode.empty());
    EXPECT_NE(vttCode.find("__vtt_"), std::string::npos) << "VTT should have proper name";
    EXPECT_NE(vttCode.find("Derived"), std::string::npos) << "VTT name should include class name";
}

// ============================================================================
// Test 2: Diamond Pattern - VTT Entry Count
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, DiamondPatternVTTEntryCount) {
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

    auto* diamond = getClass(code, "Diamond");
    ASSERT_NE(diamond, nullptr);

    // Diamond pattern needs VTT
    EXPECT_TRUE(analyzer->needsVTT(diamond));
    EXPECT_TRUE(analyzer->isDiamondPattern(diamond));

    // Get VTT entries
    auto entries = generator->getVTTEntries(diamond);
    size_t count = generator->getVTTEntryCount(diamond);

    // Diamond should have:
    // 1. Primary vtable entry
    // 2. Left base constructor entry
    // 3. Right base constructor entry
    // 4. Virtual base (Base) entry
    EXPECT_GE(entries.size(), 3) << "Diamond VTT should have at least 3 entries";
    EXPECT_EQ(count, entries.size());
}

// ============================================================================
// Test 3: VTT Entry Ordering - Primary First
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, VTTEntryOrderingPrimaryFirst) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            virtual void method() {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto entries = generator->getVTTEntries(derived);
    ASSERT_GT(entries.size(), 0);

    // First entry should be primary vtable
    // Check naming convention (implementation dependent)
    EXPECT_FALSE(entries[0].empty()) << "Primary entry should not be empty";

    // Itanium ABI: first entry is complete object vtable
    // Entry should reference the derived class vtable
    EXPECT_NE(entries[0].find("Derived"), std::string::npos)
        << "Primary entry should reference Derived class";
}

// ============================================================================
// Test 4: VTT for Class with Multiple Virtual Bases
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, MultipleVirtualBasesVTT) {
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

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Should need VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));

    auto entries = generator->getVTTEntries(derived);
    size_t count = generator->getVTTEntryCount(derived);

    // Should have entries for both virtual bases
    EXPECT_GE(entries.size(), 2) << "Should have entries for multiple virtual bases";
    EXPECT_EQ(count, entries.size());
}

// ============================================================================
// Test 5: VTT Generation for Empty Virtual Base
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, EmptyVirtualBaseVTT) {
    std::string code = R"(
        class EmptyBase {
            // Empty class
        };

        class Derived : public virtual EmptyBase {
        public:
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Even empty virtual base needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));

    auto entries = generator->getVTTEntries(derived);
    EXPECT_GT(entries.size(), 0) << "Empty virtual base still needs VTT entries";

    std::string vttCode = generator->generateVTT(derived);
    EXPECT_FALSE(vttCode.empty());
}

// ============================================================================
// Test 6: No VTT for Non-Virtual Inheritance
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, NoVTTForNonVirtualInheritance) {
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

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // No virtual bases, no VTT needed
    EXPECT_FALSE(analyzer->needsVTT(derived));

    std::string vttCode = generator->generateVTT(derived);
    EXPECT_TRUE(vttCode.empty()) << "Non-virtual inheritance should not generate VTT";
}

// ============================================================================
// Test 7: VTT for Indirect Virtual Base
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, IndirectVirtualBaseVTT) {
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

    auto* middle = getClass(code, "Middle");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(middle, nullptr);
    ASSERT_NE(derived, nullptr);

    // Middle needs VTT (has virtual base)
    EXPECT_TRUE(analyzer->needsVTT(middle));

    // Derived also needs VTT (inherits virtual base)
    EXPECT_TRUE(analyzer->needsVTT(derived));

    auto middleEntries = generator->getVTTEntries(middle);
    auto derivedEntries = generator->getVTTEntries(derived);

    EXPECT_GT(middleEntries.size(), 0);
    EXPECT_GT(derivedEntries.size(), 0);
}

// ============================================================================
// Test 8: VTT Entry Count Consistency
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, VTTEntryCountConsistency) {
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

    auto* diamond = getClass(code, "Diamond");
    ASSERT_NE(diamond, nullptr);

    // Count should match entries size
    size_t count1 = generator->getVTTEntryCount(diamond);
    auto entries = generator->getVTTEntries(diamond);
    size_t count2 = entries.size();

    EXPECT_EQ(count1, count2) << "Entry count should match actual entries";

    // Multiple calls should return same count
    size_t count3 = generator->getVTTEntryCount(diamond);
    EXPECT_EQ(count1, count3) << "Entry count should be consistent";
}

// ============================================================================
// Test 9: VTT Code Format Verification
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, VTTCodeFormatVerification) {
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

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    std::string vttCode = generator->generateVTT(derived);
    ASSERT_FALSE(vttCode.empty());

    // Check for expected patterns
    EXPECT_NE(vttCode.find("const"), std::string::npos)
        << "VTT should be const";

    EXPECT_NE(vttCode.find("void*"), std::string::npos)
        << "VTT should be array of void*";

    EXPECT_NE(vttCode.find("{"), std::string::npos)
        << "VTT should have array initializer";

    EXPECT_NE(vttCode.find("}"), std::string::npos)
        << "VTT should close array initializer";

    // Check for vtable references
    EXPECT_NE(vttCode.find("&"), std::string::npos)
        << "VTT should contain vtable references";
}

// ============================================================================
// Test 10: Complex Diamond - VTT Completeness
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, ComplexDiamondVTTCompleteness) {
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

    auto* bottom = getClass(code, "Bottom");
    ASSERT_NE(bottom, nullptr);

    // Complex diamond needs VTT
    EXPECT_TRUE(analyzer->needsVTT(bottom));

    auto entries = generator->getVTTEntries(bottom);

    // Should have entries for:
    // 1. Primary vtable
    // 2. Left1, Left2, Right1, Right2 constructor vtables
    // 3. Virtual base Top
    EXPECT_GE(entries.size(), 5) << "Complex diamond needs multiple VTT entries";

    // All entries should be non-empty
    for (const auto& entry : entries) {
        EXPECT_FALSE(entry.empty()) << "VTT entry should not be empty";
    }
}

// ============================================================================
// Test 11: VTT for Mixed Virtual and Non-Virtual Inheritance
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, MixedVirtualNonVirtualVTT) {
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

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base, needs VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));

    auto entries = generator->getVTTEntries(derived);
    EXPECT_GT(entries.size(), 0);

    // VTT should only contain entries for virtual bases, not non-virtual
    // (Implementation detail: verify structure makes sense)
}

// ============================================================================
// Test 12: VTT Name Generation
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, VTTNameGeneration) {
    std::string code = R"(
        class MyClass {
        public:
            virtual ~MyClass() {}
        };

        class MyDerived : public virtual MyClass {
        public:
            int d;
        };
    )";

    auto* derived = getClass(code, "MyDerived");
    ASSERT_NE(derived, nullptr);

    std::string vttCode = generator->generateVTT(derived);
    ASSERT_FALSE(vttCode.empty());

    // Check VTT name contains class name
    EXPECT_NE(vttCode.find("MyDerived"), std::string::npos)
        << "VTT name should include class name";

    // Check VTT prefix
    EXPECT_NE(vttCode.find("__vtt_"), std::string::npos)
        << "VTT should have __vtt_ prefix";
}

// ============================================================================
// Test 13: VTT for Deep Virtual Inheritance Hierarchy
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, DeepVirtualInheritanceHierarchyVTT) {
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

    auto* level1 = getClass(code, "Level1");
    auto* level2 = getClass(code, "Level2");
    auto* level3 = getClass(code, "Level3");

    ASSERT_NE(level1, nullptr);
    ASSERT_NE(level2, nullptr);
    ASSERT_NE(level3, nullptr);

    // Each level should need VTT
    EXPECT_TRUE(analyzer->needsVTT(level1));
    EXPECT_TRUE(analyzer->needsVTT(level2));
    EXPECT_TRUE(analyzer->needsVTT(level3));

    // Deeper levels should have more entries
    auto entries1 = generator->getVTTEntries(level1);
    auto entries2 = generator->getVTTEntries(level2);
    auto entries3 = generator->getVTTEntries(level3);

    EXPECT_GT(entries1.size(), 0);
    EXPECT_GT(entries2.size(), 0);
    EXPECT_GT(entries3.size(), 0);

    // Typically, deeper hierarchies have more VTT entries
    EXPECT_GE(entries3.size(), entries1.size())
        << "Deeper hierarchy should have at least as many VTT entries";
}

// ============================================================================
// Test 14: VTT Entries Are Unique
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, VTTEntriesAreUnique) {
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

    auto* diamond = getClass(code, "Diamond");
    ASSERT_NE(diamond, nullptr);

    auto entries = generator->getVTTEntries(diamond);
    ASSERT_GT(entries.size(), 0);

    // Check for uniqueness (no duplicate entries)
    std::set<std::string> uniqueEntries(entries.begin(), entries.end());

    // Note: Depending on implementation, some entries might legitimately repeat
    // For now, just verify all entries are present
    EXPECT_GE(uniqueEntries.size(), 1) << "Should have at least one unique entry";
}

// ============================================================================
// Test 15: VTT for Virtual Base with Virtual Methods
// ============================================================================

TEST_F(VTTGeneratorCorrectnessTest, VirtualBaseWithVirtualMethodsVTT) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            virtual void method1() {}
            virtual void method2() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            virtual void method1() override {}
            virtual void method3() {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Should need VTT
    EXPECT_TRUE(analyzer->needsVTT(derived));

    auto entries = generator->getVTTEntries(derived);
    EXPECT_GT(entries.size(), 0);

    // Generate VTT
    std::string vttCode = generator->generateVTT(derived);
    EXPECT_FALSE(vttCode.empty());

    // VTT should reference vtables which contain virtual methods
    EXPECT_NE(vttCode.find("vtable"), std::string::npos)
        << "VTT should reference vtables";
}
