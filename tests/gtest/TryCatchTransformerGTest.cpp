// TryCatchTransformerGTest.cpp - GTest migration of TryCatchTransformerTest
// Story #78: Implement setjmp/longjmp Injection for Try-Catch Blocks
// Migrated to Google Test framework

#include <gtest/gtest.h>
#include "TryCatchTransformer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <memory>
#include <string>

using namespace clang;

// Helper visitor to find try statements in AST
class TryStmtFinder : public RecursiveASTVisitor<TryStmtFinder> {
public:
    CXXTryStmt *foundTryStmt = nullptr;

    bool VisitCXXTryStmt(CXXTryStmt *tryStmt) {
        if (!foundTryStmt) {
            foundTryStmt = tryStmt;
        }
        return true;
    }
};

// Test helper: Parse C++ code and find first try statement
CXXTryStmt* parseTryStatement(const std::string& code) {
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
    if (!AST) {
        return nullptr;
    }

    TryStmtFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    return finder.foundTryStmt;
}

// Test Fixture
class TryCatchTransformerTest : public ::testing::Test {
protected:
    bool contains(const std::string& haystack, const std::string& needle) {
        return haystack.find(needle) != std::string::npos;
    }
};

// Test 1: Generate setjmp guard
TEST_F(TryCatchTransformerTest, GenerateSetjmpGuard) {
    TryCatchTransformer transformer;
    std::string result = transformer.generateSetjmpGuard("frame");

    // Should generate: if (setjmp(frame.jmpbuf) == 0)
    EXPECT_TRUE(contains(result, "setjmp"));
    EXPECT_TRUE(contains(result, "frame.jmpbuf"));
    EXPECT_TRUE(contains(result, "== 0"));
}

// Test 2: Transform basic try-catch block
TEST_F(TryCatchTransformerTest, TransformBasicTryCatch) {
    std::string code = R"(
        struct Error {
            int code;
        };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    ASSERT_NE(tryStmt, nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.transformTryCatch(tryStmt, "frame", "actions_table_0");

    // Verify key components are present
    EXPECT_TRUE(contains(result, "struct __cxx_exception_frame frame"));
    EXPECT_TRUE(contains(result, "frame.actions = actions_table_0"));
    EXPECT_TRUE(contains(result, "setjmp(frame.jmpbuf) == 0"));
    EXPECT_TRUE(contains(result, "__cxx_exception_stack = &frame"));
    EXPECT_TRUE(contains(result, "__cxx_exception_stack = frame.next"));
}

// Test 3: Generate try body with frame push/pop
TEST_F(TryCatchTransformerTest, GenerateTryBody) {
    std::string code = R"(
        void test() {
            try {
                int x = 42;
            } catch (...) {
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    ASSERT_NE(tryStmt, nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateTryBody(tryStmt, "frame");

    // Should have frame push at start and pop at end
    EXPECT_TRUE(contains(result, "__cxx_exception_stack = &frame"));
    EXPECT_TRUE(contains(result, "__cxx_exception_stack = frame.next"));
}

// Test 4: Generate catch handlers with type checking
TEST_F(TryCatchTransformerTest, GenerateCatchHandlers) {
    std::string code = R"(
        struct Error {
            int code;
        };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    ASSERT_NE(tryStmt, nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should have type check for Error
    EXPECT_TRUE(contains(result, "frame.exception_type"));
    EXPECT_TRUE(contains(result, "strcmp") || contains(result, "Error"));
}

// Test 5: Generate exception object cast
TEST_F(TryCatchTransformerTest, GenerateExceptionObjectCast) {
    std::string code = R"(
        struct Error {
            int code;
        };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    ASSERT_NE(tryStmt, nullptr);
    ASSERT_GT(tryStmt->getNumHandlers(), 0u);

    CXXCatchStmt *catchStmt = tryStmt->getHandler(0);
    VarDecl *exceptionVar = catchStmt->getExceptionDecl();
    ASSERT_NE(exceptionVar, nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateExceptionObjectCast(exceptionVar, "frame");

    // Should cast frame.exception_object to Error*
    EXPECT_TRUE(contains(result, "frame.exception_object"));
    EXPECT_TRUE(contains(result, "struct Error") || contains(result, "Error"));
}

// Test 6: Generate exception cleanup
TEST_F(TryCatchTransformerTest, GenerateExceptionCleanup) {
    std::string code = R"(
        struct Error {
            ~Error();
            int code;
        };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    ASSERT_NE(tryStmt, nullptr);
    ASSERT_GT(tryStmt->getNumHandlers(), 0u);

    CXXCatchStmt *catchStmt = tryStmt->getHandler(0);
    VarDecl *exceptionVar = catchStmt->getExceptionDecl();
    QualType exceptionType = exceptionVar->getType();

    TryCatchTransformer transformer;
    std::string result = transformer.generateExceptionCleanup(exceptionType, "e");

    // Should call destructor and free
    EXPECT_TRUE(contains(result, "dtor") || contains(result, "~"));
    EXPECT_TRUE(contains(result, "free"));
}

// Test 7: Multiple catch handlers
TEST_F(TryCatchTransformerTest, MultipleCatchHandlers) {
    std::string code = R"(
        struct Error1 { int x; };
        struct Error2 { int y; };

        void test() {
            try {
                int x = 42;
            } catch (Error1& e1) {
                int a = e1.x;
            } catch (Error2& e2) {
                int b = e2.y;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    ASSERT_NE(tryStmt, nullptr);
    EXPECT_EQ(tryStmt->getNumHandlers(), 2u);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should have type checks for both Error1 and Error2
    EXPECT_TRUE(contains(result, "Error1"));
    EXPECT_TRUE(contains(result, "Error2"));
}

// Test 8: Complete transformation integration test
TEST_F(TryCatchTransformerTest, CompleteTransformation) {
    std::string code = R"(
        struct MyError {
            int errorCode;
            ~MyError();
        };

        void mayThrow();
        void handle(int code);

        void test() {
            try {
                mayThrow();
            } catch (MyError& e) {
                handle(e.errorCode);
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    ASSERT_NE(tryStmt, nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.transformTryCatch(tryStmt, "frame", "actions_table_0");

    // Verify all key components
    EXPECT_TRUE(contains(result, "struct __cxx_exception_frame frame"));
    EXPECT_TRUE(contains(result, "frame.next = __cxx_exception_stack"));
    EXPECT_TRUE(contains(result, "frame.actions = actions_table_0"));
    EXPECT_TRUE(contains(result, "setjmp(frame.jmpbuf) == 0"));
    EXPECT_TRUE(contains(result, "__cxx_exception_stack = &frame"));
    EXPECT_TRUE(contains(result, "__cxx_exception_stack = frame.next"));
    EXPECT_TRUE(contains(result, "MyError"));
}
