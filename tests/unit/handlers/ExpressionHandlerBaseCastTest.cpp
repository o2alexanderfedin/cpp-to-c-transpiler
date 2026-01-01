/**
 * @file ExpressionHandlerBaseCastTest.cpp
 * @brief TDD tests for base cast detection in ExpressionHandler
 *
 * Part of Phase 46, Group 4, Task 9: Base Cast Detection
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (10 tests):
 *
 * CAST TYPE DETECTION (4 tests):
 * 1. DetectStaticCastToPrimaryBase - static_cast<Base1*>(derived)
 * 2. DetectStaticCastToNonPrimaryBase - static_cast<Base2*>(derived)
 * 3. DetectCStyleCastToBase - (Base1*)derived
 * 4. DetectReinterpretCastToBase - reinterpret_cast<Base2*>(derived)
 *
 * IMPLICIT CAST DETECTION (3 tests):
 * 5. DetectImplicitCastToPrimaryBase - Base1* b1 = derived (assignment)
 * 6. DetectImplicitCastToNonPrimaryBase - Base2* b2 = derived (assignment)
 * 7. DetectImplicitCastInFunctionCall - foo(derived) where foo takes Base*
 *
 * OFFSET CALCULATION (3 tests):
 * 8. CalculateZeroOffsetForPrimaryBase - primary base offset is 0
 * 9. CalculateNonZeroOffsetForNonPrimaryBase - non-primary base offset > 0
 * 10. HandleMultipleNonPrimaryBases - lpVtbl2, lpVtbl3 with correct offsets
 *
 * Expected Behavior:
 * - Detect all cast types (static_cast, reinterpret_cast, C-style, implicit)
 * - Identify target base class from cast type
 * - Determine if base is primary or non-primary
 * - Calculate correct offset using BaseOffsetCalculator
 * - Generate pointer arithmetic for non-primary bases: (Base*)((char*)derived + offset)
 */

#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "MultipleInheritanceAnalyzer.h"
#include "BaseOffsetCalculator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ExpressionHandlerBaseCastTest
 * @brief Test fixture for base cast detection
 */
class ExpressionHandlerBaseCastTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );
    }

    void TearDown() override {
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to extract cast expressions from AST
     */
    class CastExtractor : public clang::RecursiveASTVisitor<CastExtractor> {
    public:
        clang::CastExpr* foundCast = nullptr;
        std::vector<const clang::CXXRecordDecl*> foundRecords;

        bool VisitCastExpr(clang::CastExpr* CE) {
            if (!foundCast) {
                foundCast = CE;
            }
            return true;
        }

        bool VisitCXXRecordDecl(clang::CXXRecordDecl* RD) {
            if (RD->isCompleteDefinition()) {
                foundRecords.push_back(RD);
            }
            return true;
        }
    };

    /**
     * @brief Parse C++ code and extract cast expression and record declarations
     */
    std::pair<clang::CastExpr*, std::vector<const clang::CXXRecordDecl*>>
    parseCast(const std::string& code) {
        testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) {
            return {nullptr, {}};
        }

        CastExtractor extractor;
        extractor.TraverseDecl(testAST->getASTContext().getTranslationUnitDecl());
        return {extractor.foundCast, extractor.foundRecords};
    }

    // Hold the AST so we can get ASTContext later
    std::unique_ptr<clang::ASTUnit> testAST;

    /**
     * @brief Find record by name
     */
    const clang::CXXRecordDecl* findRecord(
        const std::vector<const clang::CXXRecordDecl*>& records,
        const std::string& name
    ) {
        for (auto* RD : records) {
            if (RD->getNameAsString() == name) {
                return RD;
            }
        }
        return nullptr;
    }
};

// ============================================================================
// CAST TYPE DETECTION (Tests 1-4)
// ============================================================================

/**
 * Test 1: Detect static_cast to primary base
 * C++ Input: static_cast<Base1*>(derived)
 * Expected: Detects cast, identifies Base1 as primary base (offset 0)
 */
TEST_F(ExpressionHandlerBaseCastTest, DetectStaticCastToPrimaryBase) {
    // Arrange - Create multiple inheritance hierarchy
    const std::string code = R"(
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
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived* d = new Derived();
            Base1* b1 = static_cast<Base1*>(d);
        }
    )";

    auto [castExpr, records] = parseCast(code);
    ASSERT_NE(castExpr, nullptr) << "Failed to parse cast expression";

    // Find the Derived class
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr) << "Failed to find Derived class";

    auto* base1Record = findRecord(records, "Base1");
    ASSERT_NE(base1Record, nullptr) << "Failed to find Base1 class";

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act - Analyze the base classes
    MultipleInheritanceAnalyzer analyzer(astCtx);
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify Base1 is the primary base
    auto primaryBase = analyzer.getPrimaryBase(derivedRecord);
    ASSERT_NE(primaryBase, nullptr);
    EXPECT_EQ(primaryBase->getNameAsString(), "Base1");

    // Verify offset is 0 for primary base
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base1Record);
    EXPECT_EQ(offset, 0) << "Primary base should have offset 0";

    // Verify isPrimaryBase returns true
    EXPECT_TRUE(offsetCalc.isPrimaryBase(derivedRecord, base1Record));
}

/**
 * Test 2: Detect static_cast to non-primary base
 * C++ Input: static_cast<Base2*>(derived)
 * Expected: Detects cast, identifies Base2 as non-primary base (offset > 0)
 */
TEST_F(ExpressionHandlerBaseCastTest, DetectStaticCastToNonPrimaryBase) {
    // Arrange - Create multiple inheritance hierarchy
    const std::string code = R"(
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
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived* d = new Derived();
            Base2* b2 = static_cast<Base2*>(d);
        }
    )";

    auto [castExpr, records] = parseCast(code);
    ASSERT_NE(castExpr, nullptr) << "Failed to parse cast expression";

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base2Record = findRecord(records, "Base2");
    ASSERT_NE(base2Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act - Analyze the base classes
    MultipleInheritanceAnalyzer analyzer(astCtx);
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify Base2 is NOT the primary base
    auto primaryBase = analyzer.getPrimaryBase(derivedRecord);
    ASSERT_NE(primaryBase, nullptr);
    EXPECT_NE(primaryBase->getNameAsString(), "Base2");

    // Verify offset is > 0 for non-primary base
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base2Record);
    EXPECT_GT(offset, 0) << "Non-primary base should have offset > 0";

    // Verify isPrimaryBase returns false
    EXPECT_FALSE(offsetCalc.isPrimaryBase(derivedRecord, base2Record));

    // Verify Base2 is in the non-primary bases list
    auto nonPrimaryBases = analyzer.getNonPrimaryBases(derivedRecord);
    bool foundBase2 = false;
    for (auto* base : nonPrimaryBases) {
        if (base->getNameAsString() == "Base2") {
            foundBase2 = true;
            break;
        }
    }
    EXPECT_TRUE(foundBase2) << "Base2 should be in non-primary bases";
}

/**
 * Test 3: Detect C-style cast to base
 * C++ Input: (Base1*)derived
 * Expected: Detects cast, handles like static_cast
 */
TEST_F(ExpressionHandlerBaseCastTest, DetectCStyleCastToBase) {
    // Arrange
    const std::string code = R"(
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
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived* d = new Derived();
            Base1* b1 = (Base1*)d;
        }
    )";

    auto [castExpr, records] = parseCast(code);
    ASSERT_NE(castExpr, nullptr) << "Failed to parse cast expression";

    // Verify this is a C-style cast
    EXPECT_TRUE(llvm::isa<clang::CStyleCastExpr>(castExpr))
        << "Should be CStyleCastExpr";

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base1Record = findRecord(records, "Base1");
    ASSERT_NE(base1Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify offset calculation works for C-style cast
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base1Record);
    EXPECT_EQ(offset, 0) << "Base1 is primary base, offset should be 0";
}

/**
 * Test 4: Detect reinterpret_cast to base
 * C++ Input: reinterpret_cast<Base2*>(derived)
 * Expected: Detects cast, calculates offset for non-primary base
 */
TEST_F(ExpressionHandlerBaseCastTest, DetectReinterpretCastToBase) {
    // Arrange
    const std::string code = R"(
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
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived* d = new Derived();
            Base2* b2 = reinterpret_cast<Base2*>(d);
        }
    )";

    auto [castExpr, records] = parseCast(code);
    ASSERT_NE(castExpr, nullptr) << "Failed to parse cast expression";

    // Verify this is a reinterpret_cast
    EXPECT_TRUE(llvm::isa<clang::CXXReinterpretCastExpr>(castExpr))
        << "Should be CXXReinterpretCastExpr";

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base2Record = findRecord(records, "Base2");
    ASSERT_NE(base2Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify offset calculation
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base2Record);
    EXPECT_GT(offset, 0) << "Base2 is non-primary base, offset should be > 0";
}

// ============================================================================
// IMPLICIT CAST DETECTION (Tests 5-7)
// ============================================================================

/**
 * Test 5: Detect implicit cast to primary base (assignment)
 * C++ Input: Base1* b1 = derived;
 * Expected: Detects implicit cast via ImplicitCastExpr
 */
TEST_F(ExpressionHandlerBaseCastTest, DetectImplicitCastToPrimaryBase) {
    // Arrange
    const std::string code = R"(
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
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived* d = new Derived();
            Base1* b1 = d;  // Implicit cast
        }
    )";

    auto [castExpr, records] = parseCast(code);
    ASSERT_NE(castExpr, nullptr) << "Failed to parse cast expression";

    // Implicit casts show up as ImplicitCastExpr
    EXPECT_TRUE(llvm::isa<clang::ImplicitCastExpr>(castExpr))
        << "Should be ImplicitCastExpr";

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base1Record = findRecord(records, "Base1");
    ASSERT_NE(base1Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify offset is 0 for primary base
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base1Record);
    EXPECT_EQ(offset, 0) << "Primary base offset should be 0";
}

/**
 * Test 6: Detect implicit cast to non-primary base (assignment)
 * C++ Input: Base2* b2 = derived;
 * Expected: Detects implicit cast, calculates non-zero offset
 */
TEST_F(ExpressionHandlerBaseCastTest, DetectImplicitCastToNonPrimaryBase) {
    // Arrange
    const std::string code = R"(
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
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived* d = new Derived();
            Base2* b2 = d;  // Implicit cast to non-primary base
        }
    )";

    auto [castExpr, records] = parseCast(code);
    ASSERT_NE(castExpr, nullptr) << "Failed to parse cast expression";

    // Verify implicit cast
    EXPECT_TRUE(llvm::isa<clang::ImplicitCastExpr>(castExpr))
        << "Should be ImplicitCastExpr";

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base2Record = findRecord(records, "Base2");
    ASSERT_NE(base2Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify offset is > 0 for non-primary base
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base2Record);
    EXPECT_GT(offset, 0) << "Non-primary base offset should be > 0";
}

/**
 * Test 7: Detect implicit cast in function call
 * C++ Input: foo(derived) where foo takes Base*
 * Expected: Detects implicit cast in function argument
 */
TEST_F(ExpressionHandlerBaseCastTest, DetectImplicitCastInFunctionCall) {
    // Arrange
    const std::string code = R"(
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
            void foo() override {}
            void bar() override {}
        };

        void acceptBase(Base2* b) {}

        void test() {
            Derived* d = new Derived();
            acceptBase(d);  // Implicit cast in function call
        }
    )";

    auto [castExpr, records] = parseCast(code);
    ASSERT_NE(castExpr, nullptr) << "Failed to parse cast expression";

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base2Record = findRecord(records, "Base2");
    ASSERT_NE(base2Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify offset calculation for function parameter cast
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base2Record);
    EXPECT_GT(offset, 0) << "Base2 is non-primary, offset should be > 0";
}

// ============================================================================
// OFFSET CALCULATION (Tests 8-10)
// ============================================================================

/**
 * Test 8: Calculate zero offset for primary base
 * Expected: Primary base always has offset 0
 */
TEST_F(ExpressionHandlerBaseCastTest, CalculateZeroOffsetForPrimaryBase) {
    // Arrange
    const std::string code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Derived : public Base1, public Base2 {
            int x, y;
        public:
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived* d = new Derived();
        }
    )";

    auto [castExpr, records] = parseCast(code);

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base1Record = findRecord(records, "Base1");
    ASSERT_NE(base1Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act
    MultipleInheritanceAnalyzer analyzer(astCtx);
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify Base1 is primary
    auto primaryBase = analyzer.getPrimaryBase(derivedRecord);
    ASSERT_NE(primaryBase, nullptr);
    EXPECT_EQ(primaryBase->getNameAsString(), "Base1");

    // Verify offset is exactly 0
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base1Record);
    EXPECT_EQ(offset, 0) << "Primary base must have offset 0";

    // Verify lpVtbl field offset is also 0
    uint64_t lpVtblOffset = offsetCalc.getLpVtblFieldOffset(derivedRecord, base1Record);
    EXPECT_EQ(lpVtblOffset, 0) << "Primary lpVtbl field at offset 0";
}

/**
 * Test 9: Calculate non-zero offset for non-primary base
 * Expected: Non-primary base has offset equal to sizeof(void*) = 8 bytes
 */
TEST_F(ExpressionHandlerBaseCastTest, CalculateNonZeroOffsetForNonPrimaryBase) {
    // Arrange
    const std::string code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Derived : public Base1, public Base2 {
            int x, y;
        public:
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived* d = new Derived();
        }
    )";

    auto [castExpr, records] = parseCast(code);

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base2Record = findRecord(records, "Base2");
    ASSERT_NE(base2Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify offset is > 0 for non-primary base
    uint64_t offset = offsetCalc.getBaseOffset(derivedRecord, base2Record);
    EXPECT_GT(offset, 0) << "Non-primary base must have offset > 0";

    // On 64-bit systems, offset should be sizeof(void*) = 8 bytes
    // This is the size of the first lpVtbl pointer
    EXPECT_EQ(offset, 8) << "Expected offset of 8 bytes for lpVtbl2";

    // Verify lpVtbl2 field offset
    uint64_t lpVtblOffset = offsetCalc.getLpVtblFieldOffset(derivedRecord, base2Record);
    EXPECT_EQ(lpVtblOffset, 8) << "lpVtbl2 field at offset 8";
}

/**
 * Test 10: Handle multiple non-primary bases
 * Expected: lpVtbl2 at offset 8, lpVtbl3 at offset 16
 */
TEST_F(ExpressionHandlerBaseCastTest, HandleMultipleNonPrimaryBases) {
    // Arrange
    const std::string code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Base3 {
        public:
            virtual void baz() {}
        };

        class Derived : public Base1, public Base2, public Base3 {
        public:
            void foo() override {}
            void bar() override {}
            void baz() override {}
        };

        void test() {
            Derived* d = new Derived();
        }
    )";

    auto [castExpr, records] = parseCast(code);

    // Find the classes
    auto* derivedRecord = findRecord(records, "Derived");
    ASSERT_NE(derivedRecord, nullptr);

    auto* base1Record = findRecord(records, "Base1");
    auto* base2Record = findRecord(records, "Base2");
    auto* base3Record = findRecord(records, "Base3");
    ASSERT_NE(base1Record, nullptr);
    ASSERT_NE(base2Record, nullptr);
    ASSERT_NE(base3Record, nullptr);

    // Get the AST context from the test AST
    clang::ASTContext& astCtx = testAST->getASTContext();

    // Act
    MultipleInheritanceAnalyzer analyzer(astCtx);
    BaseOffsetCalculator offsetCalc(astCtx);

    // Verify all bases are identified
    auto bases = analyzer.analyzePolymorphicBases(derivedRecord);
    EXPECT_EQ(bases.size(), 3) << "Should have 3 polymorphic bases";

    // Verify Base1 is primary (offset 0)
    uint64_t offset1 = offsetCalc.getBaseOffset(derivedRecord, base1Record);
    EXPECT_EQ(offset1, 0) << "Base1 is primary, offset 0";

    // Verify Base2 is first non-primary (offset 8, lpVtbl2)
    uint64_t offset2 = offsetCalc.getBaseOffset(derivedRecord, base2Record);
    EXPECT_EQ(offset2, 8) << "Base2 should be at offset 8 (lpVtbl2)";

    // Verify Base3 is second non-primary (offset 16, lpVtbl3)
    uint64_t offset3 = offsetCalc.getBaseOffset(derivedRecord, base3Record);
    EXPECT_EQ(offset3, 16) << "Base3 should be at offset 16 (lpVtbl3)";

    // Verify vtbl field names
    EXPECT_EQ(bases[0].VtblFieldName, "lpVtbl");
    EXPECT_EQ(bases[1].VtblFieldName, "lpVtbl2");
    EXPECT_EQ(bases[2].VtblFieldName, "lpVtbl3");
}
