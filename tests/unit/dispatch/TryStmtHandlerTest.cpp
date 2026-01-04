/**
 * @file TryStmtHandlerTest.cpp
 * @brief Unit tests for TryStmtHandler dispatcher integration
 *
 * Tests:
 * - Handler registration with dispatcher
 * - Predicate (canHandle) correctness
 * - Basic try-catch statement handling
 */

#include "dispatch/TryStmtHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "gtest/gtest.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/StmtCXX.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"

using namespace cpptoc;
using namespace clang;

class TryStmtHandlerTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Create minimal C++ code with try-catch
        std::string code = R"(
            class Error {
            public:
                Error(const char* msg) {}
            };

            void test() {
                try {
                    throw Error("test");
                } catch (Error e) {
                    // Handle error
                }
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

TEST_F(TryStmtHandlerTest, HandlerRegistration) {
    CppToCVisitorDispatcher dispatcher;

    // Registration should not throw
    EXPECT_NO_THROW(TryStmtHandler::registerWith(dispatcher));
}

TEST_F(TryStmtHandlerTest, CanHandleTryStmt) {
    // Find the try statement in the AST
    CXXTryStmt* tryStmt = nullptr;

    struct Finder : public RecursiveASTVisitor<Finder> {
        CXXTryStmt*& result;
        explicit Finder(CXXTryStmt*& r) : result(r) {}

        bool VisitCXXTryStmt(CXXTryStmt* S) {
            result = S;
            return false; // Stop traversal
        }
    } finder(tryStmt);

    finder.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());
    ASSERT_NE(tryStmt, nullptr) << "Failed to find try statement in test code";

    // Test predicate
    EXPECT_TRUE(TryStmtHandler::canHandle(tryStmt));
}

TEST_F(TryStmtHandlerTest, CannotHandleNonTryStmt) {
    // Create a simple null statement (not a try statement)
    NullStmt* nullStmt = new (cppAST->getASTContext()) NullStmt(SourceLocation());

    EXPECT_FALSE(TryStmtHandler::canHandle(nullStmt));
}

TEST_F(TryStmtHandlerTest, BasicHandling) {
    CppToCVisitorDispatcher dispatcher;
    TryStmtHandler::registerWith(dispatcher);

    // Find the try statement
    CXXTryStmt* tryStmt = nullptr;
    struct Finder : public RecursiveASTVisitor<Finder> {
        CXXTryStmt*& result;
        explicit Finder(CXXTryStmt*& r) : result(r) {}
        bool VisitCXXTryStmt(CXXTryStmt* S) {
            result = S;
            return false;
        }
    } finder(tryStmt);
    finder.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());
    ASSERT_NE(tryStmt, nullptr);

    // Handle via dispatcher
    EXPECT_NO_THROW(
        TryStmtHandler::handleTryStmt(
            dispatcher,
            cppAST->getASTContext(),
            cAST->getASTContext(),
            tryStmt
        )
    );
}

TEST_F(TryStmtHandlerTest, HandlesMultipleCatchHandlers) {
    // Create code with multiple catch handlers
    std::string code = R"(
        class Error {};
        class Warning {};

        void test() {
            try {
                throw Error();
            } catch (Error e) {
                // Handle error
            } catch (Warning w) {
                // Handle warning
            }
        }
    )";

    auto ast = tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    // Find try statement
    CXXTryStmt* tryStmt = nullptr;
    struct Finder : public RecursiveASTVisitor<Finder> {
        CXXTryStmt*& result;
        explicit Finder(CXXTryStmt*& r) : result(r) {}
        bool VisitCXXTryStmt(CXXTryStmt* S) {
            result = S;
            return false;
        }
    } finder(tryStmt);
    finder.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());
    ASSERT_NE(tryStmt, nullptr);

    // Verify it has 2 handlers
    EXPECT_EQ(tryStmt->getNumHandlers(), 2);

    // Test handling
    CppToCVisitorDispatcher dispatcher;
    TryStmtHandler::registerWith(dispatcher);

    EXPECT_NO_THROW(
        TryStmtHandler::handleTryStmt(
            dispatcher,
            ast->getASTContext(),
            cAST->getASTContext(),
            tryStmt
        )
    );
}
