/**
 * Test Suite: extern "C" Name Mangling Suppression
 *
 * Purpose: Verify that extern "C" functions are NOT mangled, while C++ functions ARE mangled.
 *
 * Test-Driven Development Phase: RED
 * - Tests written FIRST, defining expected behavior
 * - Tests will FAIL until NameMangler is modified to check isExternC()
 *
 * Milestone: #2 - Name Mangling Suppression
 * Prompt: #031 - extern "C" and Calling Convention Support
 */

#include <gtest/gtest.h>
#include "../include/NameMangler.h"
#include "../include/OverloadRegistry.h"
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <memory>
#include <string>

using namespace clang;

// Helper Functions
// ============================================================================

/**
 * Build AST from C++ code string
 */
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17", "-xc++"};
    return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}

/**
 * Find function declaration by name using AST traversal
 */
FunctionDecl* findFunction(ASTContext &Ctx, const std::string &name) {
    for (auto *D : Ctx.getTranslationUnitDecl()->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getName() == name) {
                return FD;
            }
        }
        // Check inside linkage spec decls (extern "C" blocks)
        if (auto *LS = dyn_cast<LinkageSpecDecl>(D)) {
            for (auto *LD : LS->decls()) {
                if (auto *FD = dyn_cast<FunctionDecl>(LD)) {
                    if (FD->getName() == name) {
                        return FD;
                    }
                }
            }
        }
        // Check inside namespaces
        if (auto *NS = dyn_cast<NamespaceDecl>(D)) {
            for (auto *ND : NS->decls()) {
                if (auto *FD = dyn_cast<FunctionDecl>(ND)) {
                    if (FD->getName() == name) {
                        return FD;
                    }
                }
                // Check for extern "C" inside namespace
                if (auto *LS = dyn_cast<LinkageSpecDecl>(ND)) {
                    for (auto *LD : LS->decls()) {
                        if (auto *FD = dyn_cast<FunctionDecl>(LD)) {
                            if (FD->getName() == name) {
                                return FD;
                            }
                        }
                    }
                }
            }
        }
    }
    return nullptr;
}

// ============================================================================
// Test 1: extern "C" function should NOT be mangled
// ============================================================================

// Test fixture
class ExternCManglingTest : public ::testing::Test {
protected:
};

TEST_F(ExternCManglingTest, ExternCFunctionUnmangled) {
    const char *code = R"(
            extern "C" int add(int a, int b) {
                return a + b;
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionDecl *FD = findFunction(AST->getASTContext(), "add");
        ASSERT_TRUE(FD != nullptr) << "Function 'add' not found";

        // Verify it's extern "C"
        ASSERT_TRUE(FD->isExternC()) << "Function should have C linkage";

        // Create NameMangler and check mangling
        cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
        registry.reset();
        NameMangler mangler(AST->getASTContext(), registry);
        std::string mangledName = mangler.mangleFunctionName(FD);

        // CRITICAL: extern "C" function should return UNMANGLED name
        ASSERT_TRUE(mangledName == "add") << "extern \"C\" function 'add' should NOT be mangled (expected 'add', got '" + mangledName + "');";
}

TEST_F(ExternCManglingTest, CppFunctionMangled) {
    const char *code = R"(
            void normalFunc() {
                // Regular C++ function
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionDecl *FD = findFunction(AST->getASTContext(), "normalFunc");
        ASSERT_TRUE(FD != nullptr) << "Function 'normalFunc' not found";

        // Verify it's NOT extern "C"
        ASSERT_TRUE(!FD->isExternC()) << "Function should NOT have C linkage";

        // Create NameMangler and check mangling
        cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
        registry.reset();
        NameMangler mangler(AST->getASTContext(), registry);
        std::string mangledName = mangler.mangleFunctionName(FD);

        // C++ function at global scope has no namespace, so name should be unchanged
        // (NameMangler only mangles namespaced functions)
        // For this project's NameMangler, global scope functions are NOT mangled
        ASSERT_TRUE(mangledName == "normalFunc") << "Global C++ function 'normalFunc' should not be mangled (expected 'normalFunc', got '" + mangledName + "');";
}

TEST_F(ExternCManglingTest, ExternCInNamespace) {
    const char *code = R"(
            namespace MyNS {
                extern "C" int helper() {
                    return 42;
                }
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionDecl *FD = findFunction(AST->getASTContext(), "helper");
        ASSERT_TRUE(FD != nullptr) << "Function 'helper' not found";

        // Verify it's extern "C" (even inside namespace)
        ASSERT_TRUE(FD->isExternC()) << "Function should have C linkage";

        // Create NameMangler and check mangling
        cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
        registry.reset();
        NameMangler mangler(AST->getASTContext(), registry);
        std::string mangledName = mangler.mangleFunctionName(FD);

        // CRITICAL: extern "C" suppresses namespace mangling
        ASSERT_TRUE(mangledName == "helper") << "extern \"C\" function in namespace should NOT be mangled (expected 'helper', got '" + mangledName + "');";
}

TEST_F(ExternCManglingTest, MixedNamespace) {
    const char *code = R"(
            namespace NS {
                void cppFunc() {}

                extern "C" void cFunc() {}
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        // Check C++ function
        FunctionDecl *cppFunc = findFunction(AST->getASTContext(), "cppFunc");
        ASSERT_TRUE(cppFunc != nullptr) << "Function 'cppFunc' not found";
        ASSERT_TRUE(!cppFunc->isExternC()) << "cppFunc should NOT have C linkage";

        cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
        registry.reset();
        NameMangler mangler(AST->getASTContext(), registry);
        std::string cppMangledName = mangler.mangleFunctionName(cppFunc);

        // C++ function in namespace SHOULD be mangled with namespace prefix
        ASSERT_TRUE(cppMangledName == "NS_cppFunc") << "C++ function in namespace should be mangled (expected 'NS_cppFunc', got '" + cppMangledName + "');";

        // Check extern "C" function
        FunctionDecl *cFunc = findFunction(AST->getASTContext(), "cFunc");
        ASSERT_TRUE(cFunc != nullptr) << "Function 'cFunc' not found";
        ASSERT_TRUE(cFunc->isExternC()) << "cFunc should have C linkage";

        std::string cMangledName = mangler.mangleFunctionName(cFunc);

        // extern "C" function should NOT be mangled (no namespace prefix)
        ASSERT_TRUE(cMangledName == "cFunc") << "extern \"C\" function should NOT be mangled (expected 'cFunc', got '" + cMangledName + "');";
}

TEST_F(ExternCManglingTest, ExternCNoParameterEncoding) {
    const char *code = R"(
            extern "C" void process(int x, double y) {
                // C linkage - no overloading allowed
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionDecl *FD = findFunction(AST->getASTContext(), "process");
        ASSERT_TRUE(FD != nullptr) << "Function 'process' not found";

        ASSERT_TRUE(FD->isExternC()) << "Function should have C linkage";

        cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
        registry.reset();
        NameMangler mangler(AST->getASTContext(), registry);
        std::string mangledName = mangler.mangleFunctionName(FD);

        // extern "C" function should be EXACTLY "process" - no param encoding
        ASSERT_TRUE(mangledName == "process") << "extern \"C\" should not have parameter encoding (expected 'process', got '" + mangledName + "');";
}
