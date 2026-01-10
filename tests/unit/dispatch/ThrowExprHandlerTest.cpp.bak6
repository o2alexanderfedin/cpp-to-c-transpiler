/**
 * @file ThrowExprHandlerTest.cpp
 * @brief Unit tests for ThrowExprHandler dispatcher integration
 *
 * Tests:
 * - Handler registration with dispatcher
 * - Predicate (canHandle) correctness
 * - Basic throw expression handling
 */

#include "dispatch/ThrowExprHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "../../fixtures/UnitTestHelper.h"
#include "gtest/gtest.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"

using namespace cpptoc;
using namespace clang;

class ThrowExprHandlerTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Create minimal C++ code with throw expression
        std::string code = R"(
            class Error {
            public:
                Error(const char* msg) {}
            };

            void test() {
                throw Error("test");
            }
        )";

        cppAST = tooling::buildASTFromCode(code);
        ASSERT_NE(cppAST, nullptr);

        // Create C ASTContext for target
        cAST = tooling::buildASTFromCode("void dummy() {}");
        ASSERT_NE(cAST, nullptr);
    }

    std::unique_ptr<ASTUnit> cppAST;
    std::unique_ptr<ASTUnit> cAST;
};

TEST_F(ThrowExprHandlerTest, HandlerRegistration) {
    auto ctx = test::createUnitTestContext();

    // Registration should not throw
    EXPECT_NO_THROW(ThrowExprHandler::registerWith(*ctx.dispatcher));
}

TEST_F(ThrowExprHandlerTest, CanHandleThrowExpr) {
    // Find the throw expression in the AST
    CXXThrowExpr* throwExpr = nullptr;

    struct Finder : public RecursiveASTVisitor<Finder> {
        CXXThrowExpr*& result;
        explicit Finder(CXXThrowExpr*& r) : result(r) {}

        bool VisitCXXThrowExpr(CXXThrowExpr* E) {
            result = E;
            return false; // Stop traversal
        }
    } finder(throwExpr);

    finder.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());
    ASSERT_NE(throwExpr, nullptr) << "Failed to find throw expression in test code";

    // Test predicate
    EXPECT_TRUE(ThrowExprHandler::canHandle(throwExpr));
}

TEST_F(ThrowExprHandlerTest, CannotHandleNonThrowExpr) {
    // Create a simple integer literal (not a throw expression)
    IntegerLiteral* intLit = IntegerLiteral::Create(
        cppAST->getASTContext(),
        llvm::APInt(32, 42),
        cppAST->getASTContext().IntTy,
        SourceLocation()
    );

    EXPECT_FALSE(ThrowExprHandler::canHandle(intLit));
}

TEST_F(ThrowExprHandlerTest, BasicHandling) {
    auto ctx = test::createUnitTestContext();
    ThrowExprHandler::registerWith(*ctx.dispatcher);

    // Find the throw expression
    CXXThrowExpr* throwExpr = nullptr;
    struct Finder : public RecursiveASTVisitor<Finder> {
        CXXThrowExpr*& result;
        explicit Finder(CXXThrowExpr*& r) : result(r) {}
        bool VisitCXXThrowExpr(CXXThrowExpr* E) {
            result = E;
            return false;
        }
    } finder(throwExpr);
    finder.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());
    ASSERT_NE(throwExpr, nullptr);

    // Handle via dispatcher
    EXPECT_NO_THROW(
        ThrowExprHandler::handleThrowExpr(
            *ctx.dispatcher,
            cppAST->getASTContext(),
            cAST->getASTContext(),
            throwExpr
        )
    );
}
