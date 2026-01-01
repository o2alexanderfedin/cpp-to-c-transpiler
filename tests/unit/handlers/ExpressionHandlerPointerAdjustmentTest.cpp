/**
 * @file ExpressionHandlerPointerAdjustmentTest.cpp
 * @brief TDD tests for base pointer adjustment code generation (Phase 46 Group 4 Task 11)
 *
 * Tests the actual C code generation for pointer arithmetic in base class casts.
 * Builds on Task 9's cast detection to verify the generated C expressions.
 *
 * Test Plan (10 tests):
 *
 * UPCAST CODE GENERATION (3 tests):
 * 1. GenerateUpcaestToPrimaryBase - static_cast<Base1*>(d) → (struct Base1*)d
 * 2. GenerateUpcastToNonPrimaryBase - static_cast<Base2*>(d) → (struct Base2*)((char*)d + 8)
 * 3. GenerateUpcastWithMultipleBases - Base2, Base3 with correct offsets
 *
 * DOWNCAST CODE GENERATION (2 tests):
 * 4. GenerateDowncastFromPrimaryBase - static_cast<Derived*>(b1) → (struct Derived*)b1
 * 5. GenerateDowncastFromNonPrimaryBase - static_cast<Derived*>(b2) → (struct Derived*)((char*)b2 - 8)
 *
 * CROSSCAST CODE GENERATION (2 tests):
 * 6. GenerateCrosscastBetweenBases - Base1* → Base2* (cross-cast through Derived)
 * 7. GenerateCrosscastInAssignment - b2 = (Base2*)((char*)b1 + offset)
 *
 * CONTEXT TESTING (3 tests):
 * 8. GeneratePointerAdjustmentInAssignment - Base2* b2 = d;
 * 9. GeneratePointerAdjustmentInFunctionCall - foo((Base2*)((char*)d + 8))
 * 10. GeneratePointerAdjustmentInReturnStatement - return (Base2*)((char*)d + 8);
 *
 * Expected C patterns:
 * - Primary base (offset 0): (Base1*)ptr
 * - Non-primary base (offset > 0): (Base2*)((char*)ptr + offset)
 * - Downcast from primary: (Derived*)ptr
 * - Downcast from non-primary: (Derived*)((char*)ptr - offset)
 */

#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "llvm/Support/raw_ostream.h"
#include <gtest/gtest.h>
#include <memory>
#include <sstream>

using namespace cpptoc;

/**
 * @class ExpressionHandlerPointerAdjustmentTest
 * @brief Test fixture for pointer adjustment code generation
 */
class ExpressionHandlerPointerAdjustmentTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;
    std::unique_ptr<ExpressionHandler> handler;

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
        handler = std::make_unique<ExpressionHandler>();
    }

    void TearDown() override {
        handler.reset();
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
        std::vector<clang::CastExpr*> casts;

        bool VisitCastExpr(clang::CastExpr* CE) {
            casts.push_back(CE);
            return true;
        }
    };

    /**
     * @brief Parse C++ code and extract all cast expressions
     */
    std::vector<clang::CastExpr*> parseCasts(const std::string& code) {
        testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) {
            return {};
        }

        CastExtractor extractor;
        extractor.TraverseDecl(testAST->getASTContext().getTranslationUnitDecl());
        return extractor.casts;
    }

    /**
     * @brief Translate cast expression and generate C code using Clang's printing
     */
    std::string translateCastToC(clang::CastExpr* CE) {
        if (!CE) {
            return "";
        }

        // Create a new context using the test AST
        auto testBuilder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        auto testContext = std::make_unique<HandlerContext>(
            testAST->getASTContext(),
            cAST->getASTContext(),
            *testBuilder
        );

        // Translate the cast expression
        clang::Expr* translatedExpr = handler->handleExpr(CE, *testContext);
        if (!translatedExpr) {
            return "";
        }

        // Generate C code using Clang's expression printing
        std::string result;
        llvm::raw_string_ostream os(result);

        clang::PrintingPolicy policy(cAST->getASTContext().getLangOpts());
        policy.SuppressTagKeyword = false;  // Keep 'struct' keyword

        translatedExpr->printPretty(os, nullptr, policy);
        os.flush();

        return result;
    }

    // Hold the test AST
    std::unique_ptr<clang::ASTUnit> testAST;
};

// ============================================================================
// UPCAST CODE GENERATION (Tests 1-3)
// ============================================================================

/**
 * Test 1: Generate upcast to primary base (no offset)
 * C++ Input: static_cast<Base1*>(d)
 * Expected C: (struct Base1*)d
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GenerateUpcastToPrimaryBase) {
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
            Base1* b1 = static_cast<Base1*>(d);
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the static_cast (should be the last cast, after implicit new cast)
    clang::CastExpr* staticCast = nullptr;
    for (auto* cast : casts) {
        if (llvm::isa<clang::CXXStaticCastExpr>(cast)) {
            staticCast = cast;
            break;
        }
    }
    ASSERT_NE(staticCast, nullptr) << "static_cast not found";

    // Act - Translate to C
    std::string cCode = translateCastToC(staticCast);

    // Assert
    // Primary base should generate: (struct Base1*)d
    // No pointer arithmetic needed
    EXPECT_TRUE(cCode.find("(") != std::string::npos) << "Expected cast expression";
    EXPECT_TRUE(cCode.find("Base1") != std::string::npos) << "Expected Base1 type";
    EXPECT_FALSE(cCode.find("char*") != std::string::npos) << "Should not have char* cast for primary base";
    EXPECT_FALSE(cCode.find("+") != std::string::npos) << "Should not have pointer arithmetic for primary base";
}

/**
 * Test 2: Generate upcast to non-primary base (with offset)
 * C++ Input: static_cast<Base2*>(d)
 * Expected C: (struct Base2*)((char*)d + 8)
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GenerateUpcastToNonPrimaryBase) {
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
            Base2* b2 = static_cast<Base2*>(d);
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the static_cast to Base2*
    clang::CastExpr* staticCast = nullptr;
    for (auto* cast : casts) {
        if (auto* SCE = llvm::dyn_cast<clang::CXXStaticCastExpr>(cast)) {
            if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()) {
                if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()->getNameAsString() == "Base2") {
                    staticCast = SCE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(staticCast, nullptr) << "static_cast<Base2*> not found";

    // Act - Translate to C
    std::string cCode = translateCastToC(staticCast);

    // Assert
    // Non-primary base should generate: (struct Base2*)((char*)d + 8)
    EXPECT_TRUE(cCode.find("Base2") != std::string::npos) << "Expected Base2 type, got: " << cCode;
    EXPECT_TRUE(cCode.find("char") != std::string::npos) << "Expected char* cast for pointer arithmetic, got: " << cCode;
    EXPECT_TRUE(cCode.find("+") != std::string::npos) << "Expected pointer arithmetic (+), got: " << cCode;
    EXPECT_TRUE(cCode.find("8") != std::string::npos) << "Expected offset of 8 bytes, got: " << cCode;
}

/**
 * Test 3: Generate upcast with multiple non-primary bases
 * C++ Input: static_cast<Base3*>(d)
 * Expected C: (struct Base3*)((char*)d + 16)
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GenerateUpcastWithMultipleBases) {
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
            Base3* b3 = static_cast<Base3*>(d);
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the static_cast to Base3*
    clang::CastExpr* staticCast = nullptr;
    for (auto* cast : casts) {
        if (auto* SCE = llvm::dyn_cast<clang::CXXStaticCastExpr>(cast)) {
            if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()) {
                if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()->getNameAsString() == "Base3") {
                    staticCast = SCE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(staticCast, nullptr) << "static_cast<Base3*> not found";

    // Act - Translate to C
    std::string cCode = translateCastToC(staticCast);

    // Assert
    // Base3 is the second non-primary base, offset should be 16 (8 + 8)
    EXPECT_TRUE(cCode.find("Base3") != std::string::npos) << "Expected Base3 type";
    EXPECT_TRUE(cCode.find("char") != std::string::npos) << "Expected char* cast";
    EXPECT_TRUE(cCode.find("+") != std::string::npos) << "Expected pointer arithmetic";
    EXPECT_TRUE(cCode.find("16") != std::string::npos) << "Expected offset of 16 bytes";
}

// ============================================================================
// DOWNCAST CODE GENERATION (Tests 4-5)
// ============================================================================

/**
 * Test 4: Generate downcast from primary base (no offset)
 * C++ Input: static_cast<Derived*>(b1)
 * Expected C: (struct Derived*)b1
 *
 * NOTE: In C++, downcasts from primary base require no adjustment because
 * the primary base is at offset 0 in the derived class.
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GenerateDowncastFromPrimaryBase) {
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
            Base1* b1 = new Derived();
            Derived* d = static_cast<Derived*>(b1);
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the static_cast to Derived* (should be the last cast)
    clang::CastExpr* staticCast = nullptr;
    for (auto* cast : casts) {
        if (auto* SCE = llvm::dyn_cast<clang::CXXStaticCastExpr>(cast)) {
            if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()) {
                if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()->getNameAsString() == "Derived") {
                    staticCast = SCE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(staticCast, nullptr) << "static_cast<Derived*> not found";

    // Act - Translate to C
    std::string cCode = translateCastToC(staticCast);

    // Assert
    // Downcast from primary base should generate: (struct Derived*)b1
    // No offset adjustment needed
    EXPECT_TRUE(cCode.find("Derived") != std::string::npos) << "Expected Derived type";
    EXPECT_FALSE(cCode.find("char*") != std::string::npos) << "Should not have char* cast for primary base downcast";
    EXPECT_FALSE(cCode.find("+") != std::string::npos) << "Should not have pointer arithmetic for primary base";
    EXPECT_FALSE(cCode.find("-") != std::string::npos) << "Should not have pointer arithmetic for primary base";
}

/**
 * Test 5: Generate downcast from non-primary base (with negative offset)
 * C++ Input: static_cast<Derived*>(b2)
 * Expected C: (struct Derived*)((char*)b2 - 8)
 *
 * NOTE: Downcasting from non-primary base requires subtracting the offset
 * to get back to the derived object's address.
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GenerateDowncastFromNonPrimaryBase) {
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
            Base2* b2 = new Derived();
            Derived* d = static_cast<Derived*>(b2);
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the static_cast to Derived* from Base2*
    clang::CastExpr* staticCast = nullptr;
    for (auto* cast : casts) {
        if (auto* SCE = llvm::dyn_cast<clang::CXXStaticCastExpr>(cast)) {
            if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()) {
                if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()->getNameAsString() == "Derived") {
                    staticCast = SCE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(staticCast, nullptr) << "static_cast<Derived*> not found";

    // Act - Translate to C
    std::string cCode = translateCastToC(staticCast);

    // Assert
    // Downcast from non-primary base should generate: (struct Derived*)((char*)b2 - 8)
    EXPECT_TRUE(cCode.find("Derived") != std::string::npos) << "Expected Derived type";
    EXPECT_TRUE(cCode.find("char") != std::string::npos) << "Expected char* cast for pointer arithmetic";
    EXPECT_TRUE(cCode.find("-") != std::string::npos || cCode.find("+ -") != std::string::npos)
        << "Expected pointer arithmetic with negative offset";
}

// ============================================================================
// CROSSCAST CODE GENERATION (Tests 6-7)
// ============================================================================

/**
 * Test 6: Generate crosscast between bases
 * C++ Input: Base1* b1 = ...; Base2* b2 = static_cast<Base2*>(static_cast<Derived*>(b1));
 * Expected C: (struct Base2*)((char*)(struct Derived*)b1 + 8)
 *
 * NOTE: Crosscasting requires two steps:
 * 1. Downcast to Derived
 * 2. Upcast to target base
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GenerateCrosscastBetweenBases) {
    // Arrange - Create crosscast via explicit double cast
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
            Base1* b1 = new Derived();
            // Crosscast: Base1* → Derived* → Base2*
            Base2* b2 = static_cast<Base2*>(static_cast<Derived*>(b1));
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the outer static_cast to Base2* (should be last)
    clang::CastExpr* outerCast = nullptr;
    for (auto it = casts.rbegin(); it != casts.rend(); ++it) {
        if (auto* SCE = llvm::dyn_cast<clang::CXXStaticCastExpr>(*it)) {
            if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()) {
                if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()->getNameAsString() == "Base2") {
                    outerCast = SCE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(outerCast, nullptr) << "Outer static_cast<Base2*> not found";

    // Act - Translate to C
    std::string cCode = translateCastToC(outerCast);

    // Assert
    // Should generate nested casts with offset adjustment
    EXPECT_TRUE(cCode.find("Base2") != std::string::npos) << "Expected Base2 type";
    EXPECT_TRUE(cCode.find("Derived") != std::string::npos) << "Expected intermediate Derived cast";
    EXPECT_TRUE(cCode.find("char") != std::string::npos) << "Expected char* cast for offset";
    EXPECT_TRUE(cCode.find("+") != std::string::npos) << "Expected pointer arithmetic";
}

/**
 * Test 7: Generate crosscast in assignment
 * C++ Input: b2 = static_cast<Base2*>(b1);  (where both are base pointers)
 * Expected C: b2 = (struct Base2*)((char*)(struct Derived*)b1 + 8);
 *
 * NOTE: C++ allows direct crosscast, but C requires explicit downcast then upcast
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GenerateCrosscastInAssignment) {
    // For C++, we need to use static_cast through Derived explicitly
    // Direct crosscast Base1* → Base2* is not allowed in standard C++

    // This test is similar to Test 6 but focuses on assignment context
    // We'll use the same approach: explicit double cast

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
            Base1* b1 = new Derived();
            Base2* b2 = nullptr;
            b2 = static_cast<Base2*>(static_cast<Derived*>(b1));
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the assignment's outer cast
    clang::CastExpr* outerCast = nullptr;
    for (auto it = casts.rbegin(); it != casts.rend(); ++it) {
        if (auto* SCE = llvm::dyn_cast<clang::CXXStaticCastExpr>(*it)) {
            if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()) {
                if (SCE->getType()->getPointeeType()->getAsCXXRecordDecl()->getNameAsString() == "Base2") {
                    outerCast = SCE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(outerCast, nullptr) << "static_cast<Base2*> in assignment not found";

    // Act
    std::string cCode = translateCastToC(outerCast);

    // Assert
    EXPECT_TRUE(cCode.find("Base2") != std::string::npos) << "Expected Base2 type";
    EXPECT_TRUE(cCode.find("char") != std::string::npos) << "Expected char* cast";
    EXPECT_TRUE(cCode.find("+") != std::string::npos) << "Expected offset addition";
}

// ============================================================================
// CONTEXT TESTING (Tests 8-10)
// ============================================================================

/**
 * Test 8: Generate pointer adjustment in assignment
 * C++ Input: Base2* b2 = d;  (implicit cast)
 * Expected C: Base2* b2 = (struct Base2*)((char*)d + 8);
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GeneratePointerAdjustmentInAssignment) {
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
            Base2* b2 = d;  // Implicit upcast
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the implicit cast to Base2*
    clang::CastExpr* implicitCast = nullptr;
    for (auto* cast : casts) {
        if (auto* ICE = llvm::dyn_cast<clang::ImplicitCastExpr>(cast)) {
            if (ICE->getType()->isPointerType()) {
                auto* recordType = ICE->getType()->getPointeeType()->getAsCXXRecordDecl();
                if (recordType && recordType->getNameAsString() == "Base2") {
                    implicitCast = ICE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(implicitCast, nullptr) << "Implicit cast to Base2* not found";

    // Act
    std::string cCode = translateCastToC(implicitCast);

    // Assert
    // Implicit upcast should still generate pointer arithmetic
    EXPECT_TRUE(cCode.find("Base2") != std::string::npos) << "Expected Base2 type";
    EXPECT_TRUE(cCode.find("char") != std::string::npos) << "Expected char* cast";
    EXPECT_TRUE(cCode.find("+") != std::string::npos) << "Expected pointer arithmetic";
}

/**
 * Test 9: Generate pointer adjustment in function call
 * C++ Input: acceptBase(d);  where acceptBase takes Base2*
 * Expected C: acceptBase((struct Base2*)((char*)d + 8));
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GeneratePointerAdjustmentInFunctionCall) {
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
            acceptBase(d);  // Implicit upcast in function call
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the implicit cast in function argument
    clang::CastExpr* implicitCast = nullptr;
    for (auto* cast : casts) {
        if (auto* ICE = llvm::dyn_cast<clang::ImplicitCastExpr>(cast)) {
            if (ICE->getType()->isPointerType()) {
                auto* recordType = ICE->getType()->getPointeeType()->getAsCXXRecordDecl();
                if (recordType && recordType->getNameAsString() == "Base2") {
                    implicitCast = ICE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(implicitCast, nullptr) << "Implicit cast in function call not found";

    // Act
    std::string cCode = translateCastToC(implicitCast);

    // Assert
    EXPECT_TRUE(cCode.find("Base2") != std::string::npos) << "Expected Base2 type";
    EXPECT_TRUE(cCode.find("char") != std::string::npos) << "Expected char* cast";
    EXPECT_TRUE(cCode.find("+") != std::string::npos) << "Expected pointer arithmetic";
}

/**
 * Test 10: Generate pointer adjustment in return statement
 * C++ Input: return d;  where function returns Base2*
 * Expected C: return (struct Base2*)((char*)d + 8);
 */
TEST_F(ExpressionHandlerPointerAdjustmentTest, GeneratePointerAdjustmentInReturnStatement) {
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

        Base2* getBase() {
            Derived* d = new Derived();
            return d;  // Implicit upcast in return
        }
    )";

    auto casts = parseCasts(code);
    ASSERT_FALSE(casts.empty()) << "No casts found in code";

    // Find the implicit cast in return statement
    clang::CastExpr* implicitCast = nullptr;
    for (auto* cast : casts) {
        if (auto* ICE = llvm::dyn_cast<clang::ImplicitCastExpr>(cast)) {
            if (ICE->getType()->isPointerType()) {
                auto* recordType = ICE->getType()->getPointeeType()->getAsCXXRecordDecl();
                if (recordType && recordType->getNameAsString() == "Base2") {
                    implicitCast = ICE;
                    break;
                }
            }
        }
    }
    ASSERT_NE(implicitCast, nullptr) << "Implicit cast in return statement not found";

    // Act
    std::string cCode = translateCastToC(implicitCast);

    // Assert
    EXPECT_TRUE(cCode.find("Base2") != std::string::npos) << "Expected Base2 type";
    EXPECT_TRUE(cCode.find("char") != std::string::npos) << "Expected char* cast";
    EXPECT_TRUE(cCode.find("+") != std::string::npos) << "Expected pointer arithmetic";
}
