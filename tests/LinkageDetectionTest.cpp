// TDD Tests for extern "C" Linkage Detection - Milestone 1
// Tests the ability to detect and query language linkage (extern "C" vs C++)

#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <iostream>

using namespace clang;
using namespace clang::ast_matchers;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}

// Helper to find function by name
FunctionDecl* findFunction(ASTContext &Ctx, const std::string& name) {
    auto Matcher = functionDecl(hasName(name)).bind("func");
    auto Matches = match(Matcher, Ctx);
    if (Matches.empty()) return nullptr;
    return const_cast<FunctionDecl*>(Matches[0].getNodeAs<FunctionDecl>("func"));
}

// ============================================================================
// Test 1: Simple extern "C" function
// ============================================================================
void test_SimpleExternCFunction() {
    TEST_START("SimpleExternCFunction: extern \"C\" int add(int,int)");

    const char *code = R"(
        extern "C" int add(int a, int b) {
            return a + b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl* FD = findFunction(AST->getASTContext(), "add");
    ASSERT(FD != nullptr, "Function 'add' not found");

    // Test: Function should have C linkage
    ASSERT(FD->isExternC(), "Function should have C linkage");
    ASSERT(FD->getLanguageLinkage() == CLanguageLinkage,
           "Language linkage should be CLanguageLinkage");

    TEST_PASS("SimpleExternCFunction");
}

// ============================================================================
// Test 2: extern "C" block with multiple functions
// ============================================================================
void test_ExternCBlock() {
    TEST_START("ExternCBlock: multiple functions in extern \"C\" { }");

    const char *code = R"(
        extern "C" {
            void init();
            void cleanup();
            int process(int x);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    // All three functions should have C linkage
    FunctionDecl* init = findFunction(AST->getASTContext(), "init");
    FunctionDecl* cleanup = findFunction(AST->getASTContext(), "cleanup");
    FunctionDecl* process = findFunction(AST->getASTContext(), "process");

    ASSERT(init != nullptr, "init() not found");
    ASSERT(cleanup != nullptr, "cleanup() not found");
    ASSERT(process != nullptr, "process() not found");

    ASSERT(init->isExternC(), "init() should have C linkage");
    ASSERT(cleanup->isExternC(), "cleanup() should have C linkage");
    ASSERT(process->isExternC(), "process() should have C linkage");

    TEST_PASS("ExternCBlock");
}

// ============================================================================
// Test 3: Mixed C and C++ linkage
// ============================================================================
void test_MixedLinkage() {
    TEST_START("MixedLinkage: C and C++ functions in same file");

    const char *code = R"(
        extern "C" void c_func();

        namespace NS {
            void cpp_func();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl* c_func = findFunction(AST->getASTContext(), "c_func");
    FunctionDecl* cpp_func = findFunction(AST->getASTContext(), "cpp_func");

    ASSERT(c_func != nullptr, "c_func() not found");
    ASSERT(cpp_func != nullptr, "cpp_func() not found");

    // c_func should have C linkage
    ASSERT(c_func->isExternC(), "c_func() should have C linkage");
    ASSERT(c_func->getLanguageLinkage() == CLanguageLinkage,
           "c_func() should have CLanguageLinkage");

    // cpp_func should have C++ linkage
    ASSERT(!cpp_func->isExternC(), "cpp_func() should NOT have C linkage");
    ASSERT(cpp_func->getLanguageLinkage() == CXXLanguageLinkage,
           "cpp_func() should have CXXLanguageLinkage");

    TEST_PASS("MixedLinkage");
}

// ============================================================================
// Test 4: extern "C" with namespace
// ============================================================================
void test_ExternCWithNamespace() {
    TEST_START("ExternCWithNamespace: extern \"C\" inside namespace");

    const char *code = R"(
        namespace MyNS {
            extern "C" void foo();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl* foo = findFunction(AST->getASTContext(), "foo");
    ASSERT(foo != nullptr, "foo() not found");

    // Function should have C linkage despite being in namespace
    ASSERT(foo->isExternC(),
           "foo() should have C linkage (namespace is ignored)");

    TEST_PASS("ExternCWithNamespace");
}

// ============================================================================
// Test 5: extern "C" static function
// ============================================================================
void test_ExternCStaticFunction() {
    TEST_START("ExternCStaticFunction: static function with C linkage");

    const char *code = R"(
        extern "C" {
            static void helper() {
                // internal linkage + C language linkage
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl* helper = findFunction(AST->getASTContext(), "helper");
    ASSERT(helper != nullptr, "helper() not found");

    // IMPORTANT: Static functions inside extern "C" blocks have NoLanguageLinkage
    // because static implies internal linkage - the function is not externally visible,
    // so language linkage (which affects external name mangling) does not apply.
    // This is correct Clang behavior.
    ASSERT(!helper->isExternC(),
           "static helper() should NOT have extern C linkage");
    ASSERT(helper->getLanguageLinkage() == NoLanguageLinkage,
           "static helper() should have NoLanguageLinkage");

    // Should have static storage class (internal linkage)
    ASSERT(helper->getStorageClass() == SC_Static,
           "helper() should have static storage class");

    TEST_PASS("ExternCStaticFunction");
}

// ============================================================================
// Test 6: C++ function (default linkage)
// ============================================================================
void test_CppFunctionDefaultLinkage() {
    TEST_START("CppFunctionDefaultLinkage: regular C++ function");

    const char *code = R"(
        void normalFunc() {
            // Regular C++ function
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl* normalFunc = findFunction(AST->getASTContext(), "normalFunc");
    ASSERT(normalFunc != nullptr, "normalFunc() not found");

    // Should have C++ linkage by default
    ASSERT(!normalFunc->isExternC(),
           "normalFunc() should NOT have C linkage");
    ASSERT(normalFunc->getLanguageLinkage() == CXXLanguageLinkage,
           "normalFunc() should have CXXLanguageLinkage");

    TEST_PASS("CppFunctionDefaultLinkage");
}

// ============================================================================
// Main function
// ============================================================================
int main() {
    std::cout << "=== extern \"C\" Linkage Detection Tests ===" << std::endl;
    std::cout << std::endl;

    test_SimpleExternCFunction();
    test_ExternCBlock();
    test_MixedLinkage();
    test_ExternCWithNamespace();
    test_ExternCStaticFunction();
    test_CppFunctionDefaultLinkage();

    std::cout << std::endl;
    std::cout << "===========================================" << std::endl;
    std::cout << "Tests passed: " << tests_passed << std::endl;
    std::cout << "Tests failed: " << tests_failed << std::endl;
    std::cout << "===========================================" << std::endl;

    return (tests_failed == 0) ? 0 : 1;
}
