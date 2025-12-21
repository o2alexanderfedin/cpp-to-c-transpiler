// tests/LinkageDetectionTest_GTest.cpp
// Migrated from LinkageDetectionTest.cpp to Google Test framework
// TDD Tests for extern "C" Linkage Detection - Milestone 1

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "../include/CppToCVisitor.h"
#include "../include/CNodeBuilder.h"

using namespace clang;
using namespace clang::ast_matchers;

// Test fixture for Linkage Detection tests
class LinkageDetectionTestFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
        std::vector<std::string> args = {"-std=c++17"};
        return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    }

    FunctionDecl* findFunction(ASTContext &Ctx, const std::string& name) {
        auto Matcher = functionDecl(hasName(name)).bind("func");
        auto Matches = match(Matcher, Ctx);
        if (Matches.empty()) return nullptr;
        return const_cast<FunctionDecl*>(Matches[0].getNodeAs<FunctionDecl>("func"));
    }
};

// Test 1: Simple extern "C" function
TEST_F(LinkageDetectionTestFixture, SimpleExternCFunction) {
    const char *code = R"(
        extern "C" int add(int a, int b) {
            return a + b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* FD = findFunction(AST->getASTContext(), "add");
    ASSERT_NE(FD, nullptr) << "Function 'add' not found";

    // Test: Function should have C linkage
    ASSERT_TRUE(FD->isExternC()) << "Function should have C linkage";
    ASSERT_EQ(FD->getLanguageLinkage(), CLanguageLinkage)
           << "Language linkage should be CLanguageLinkage";
}

// Test 2: extern "C" block with multiple functions
TEST_F(LinkageDetectionTestFixture, ExternCBlock) {
    const char *code = R"(
        extern "C" {
            void init();
            void cleanup();
            int process(int x);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // All three functions should have C linkage
    FunctionDecl* init = findFunction(AST->getASTContext(), "init");
    FunctionDecl* cleanup = findFunction(AST->getASTContext(), "cleanup");
    FunctionDecl* process = findFunction(AST->getASTContext(), "process");

    ASSERT_NE(init, nullptr) << "init() not found";
    ASSERT_NE(cleanup, nullptr) << "cleanup() not found";
    ASSERT_NE(process, nullptr) << "process() not found";

    ASSERT_TRUE(init->isExternC()) << "init() should have C linkage";
    ASSERT_TRUE(cleanup->isExternC()) << "cleanup() should have C linkage";
    ASSERT_TRUE(process->isExternC()) << "process() should have C linkage";
}

// Test 3: Mixed C and C++ linkage
TEST_F(LinkageDetectionTestFixture, MixedLinkage) {
    const char *code = R"(
        extern "C" void c_func();

        namespace NS {
            void cpp_func();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* c_func = findFunction(AST->getASTContext(), "c_func");
    FunctionDecl* cpp_func = findFunction(AST->getASTContext(), "cpp_func");

    ASSERT_NE(c_func, nullptr) << "c_func() not found";
    ASSERT_NE(cpp_func, nullptr) << "cpp_func() not found";

    // c_func should have C linkage
    ASSERT_TRUE(c_func->isExternC()) << "c_func() should have C linkage";
    ASSERT_EQ(c_func->getLanguageLinkage(), CLanguageLinkage)
           << "c_func() should have CLanguageLinkage";

    // cpp_func should have C++ linkage
    ASSERT_FALSE(cpp_func->isExternC()) << "cpp_func() should NOT have C linkage";
    ASSERT_EQ(cpp_func->getLanguageLinkage(), CXXLanguageLinkage)
           << "cpp_func() should have CXXLanguageLinkage";
}

// Test 4: extern "C" with namespace
TEST_F(LinkageDetectionTestFixture, ExternCWithNamespace) {
    const char *code = R"(
        namespace MyNS {
            extern "C" void foo();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* foo = findFunction(AST->getASTContext(), "foo");
    ASSERT_NE(foo, nullptr) << "foo() not found";

    // Function should have C linkage despite being in namespace
    ASSERT_TRUE(foo->isExternC())
           << "foo() should have C linkage (namespace is ignored)";
}

// Test 5: extern "C" static function
TEST_F(LinkageDetectionTestFixture, ExternCStaticFunction) {
    const char *code = R"(
        extern "C" {
            static void helper() {
                // internal linkage + C language linkage
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* helper = findFunction(AST->getASTContext(), "helper");
    ASSERT_NE(helper, nullptr) << "helper() not found";

    // IMPORTANT: Static functions inside extern "C" blocks have NoLanguageLinkage
    // because static implies internal linkage - the function is not externally visible,
    // so language linkage (which affects external name mangling) does not apply.
    // This is correct Clang behavior.
    ASSERT_FALSE(helper->isExternC())
           << "static helper() should NOT have extern C linkage";
    ASSERT_EQ(helper->getLanguageLinkage(), NoLanguageLinkage)
           << "static helper() should have NoLanguageLinkage";

    // Should have static storage class (internal linkage)
    ASSERT_EQ(helper->getStorageClass(), SC_Static)
           << "helper() should have static storage class";
}

// Test 6: C++ function (default linkage)
TEST_F(LinkageDetectionTestFixture, CppFunctionDefaultLinkage) {
    const char *code = R"(
        void normalFunc() {
            // Regular C++ function
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* normalFunc = findFunction(AST->getASTContext(), "normalFunc");
    ASSERT_NE(normalFunc, nullptr) << "normalFunc() not found";

    // Should have C++ linkage by default
    ASSERT_FALSE(normalFunc->isExternC())
           << "normalFunc() should NOT have C linkage";
    ASSERT_EQ(normalFunc->getLanguageLinkage(), CXXLanguageLinkage)
           << "normalFunc() should have CXXLanguageLinkage";
}
