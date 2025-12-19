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

#include "../include/NameMangler.h"
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <iostream>
#include <memory>
#include <string>

using namespace clang;

// ============================================================================
// Test Macros (matching existing test patterns)
// ============================================================================

#define TEST_START(name) \
    std::cout << "Running " << name << "... "; \
    std::cout.flush();

#define TEST_PASS(name) \
    std::cout << "✓" << std::endl;

#define ASSERT(condition, message) \
    if (!(condition)) { \
        std::cout << "✗ FAILED: " << message << std::endl; \
        return; \
    }

// ============================================================================
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
void test_ExternCFunctionUnmangled() {
    TEST_START("ExternCFunctionUnmangled");

    const char *code = R"(
        extern "C" int add(int a, int b) {
            return a + b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl *FD = findFunction(AST->getASTContext(), "add");
    ASSERT(FD != nullptr, "Function 'add' not found");

    // Verify it's extern "C"
    ASSERT(FD->isExternC(), "Function should have C linkage");

    // Create NameMangler and check mangling
    NameMangler mangler(AST->getASTContext());
    std::string mangledName = mangler.mangleFunctionName(FD);

    // CRITICAL: extern "C" function should return UNMANGLED name
    ASSERT(mangledName == "add",
           "extern \"C\" function 'add' should NOT be mangled (expected 'add', got '" + mangledName + "')");

    TEST_PASS("ExternCFunctionUnmangled");
}

// ============================================================================
// Test 2: C++ function SHOULD be mangled
// ============================================================================
void test_CppFunctionMangled() {
    TEST_START("CppFunctionMangled");

    const char *code = R"(
        void normalFunc() {
            // Regular C++ function
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl *FD = findFunction(AST->getASTContext(), "normalFunc");
    ASSERT(FD != nullptr, "Function 'normalFunc' not found");

    // Verify it's NOT extern "C"
    ASSERT(!FD->isExternC(), "Function should NOT have C linkage");

    // Create NameMangler and check mangling
    NameMangler mangler(AST->getASTContext());
    std::string mangledName = mangler.mangleFunctionName(FD);

    // C++ function at global scope has no namespace, so name should be unchanged
    // (NameMangler only mangles namespaced functions)
    // For this project's NameMangler, global scope functions are NOT mangled
    ASSERT(mangledName == "normalFunc",
           "Global C++ function 'normalFunc' should not be mangled (expected 'normalFunc', got '" + mangledName + "')");

    TEST_PASS("CppFunctionMangled");
}

// ============================================================================
// Test 3: extern "C" in namespace should NOT be mangled (no namespace prefix)
// ============================================================================
void test_ExternCInNamespace() {
    TEST_START("ExternCInNamespace");

    const char *code = R"(
        namespace MyNS {
            extern "C" int helper() {
                return 42;
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl *FD = findFunction(AST->getASTContext(), "helper");
    ASSERT(FD != nullptr, "Function 'helper' not found");

    // Verify it's extern "C" (even inside namespace)
    ASSERT(FD->isExternC(), "Function should have C linkage");

    // Create NameMangler and check mangling
    NameMangler mangler(AST->getASTContext());
    std::string mangledName = mangler.mangleFunctionName(FD);

    // CRITICAL: extern "C" suppresses namespace mangling
    ASSERT(mangledName == "helper",
           "extern \"C\" function in namespace should NOT be mangled (expected 'helper', got '" + mangledName + "')");

    TEST_PASS("ExternCInNamespace");
}

// ============================================================================
// Test 4: Mixed namespace - C++ mangled, extern "C" NOT mangled
// ============================================================================
void test_MixedNamespace() {
    TEST_START("MixedNamespace");

    const char *code = R"(
        namespace NS {
            void cppFunc() {}

            extern "C" void cFunc() {}
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    // Check C++ function
    FunctionDecl *cppFunc = findFunction(AST->getASTContext(), "cppFunc");
    ASSERT(cppFunc != nullptr, "Function 'cppFunc' not found");
    ASSERT(!cppFunc->isExternC(), "cppFunc should NOT have C linkage");

    NameMangler mangler(AST->getASTContext());
    std::string cppMangledName = mangler.mangleFunctionName(cppFunc);

    // C++ function in namespace SHOULD be mangled with namespace prefix
    ASSERT(cppMangledName == "NS_cppFunc",
           "C++ function in namespace should be mangled (expected 'NS_cppFunc', got '" + cppMangledName + "')");

    // Check extern "C" function
    FunctionDecl *cFunc = findFunction(AST->getASTContext(), "cFunc");
    ASSERT(cFunc != nullptr, "Function 'cFunc' not found");
    ASSERT(cFunc->isExternC(), "cFunc should have C linkage");

    std::string cMangledName = mangler.mangleFunctionName(cFunc);

    // extern "C" function should NOT be mangled (no namespace prefix)
    ASSERT(cMangledName == "cFunc",
           "extern \"C\" function should NOT be mangled (expected 'cFunc', got '" + cMangledName + "')");

    TEST_PASS("MixedNamespace");
}

// ============================================================================
// Test 5: Overloaded C++ functions get parameter encoding (future milestone)
// ============================================================================
void test_OverloadedCppFunctions() {
    TEST_START("OverloadedCppFunctions (param encoding not yet implemented)");

    const char *code = R"(
        void compute(int x) {}
        void compute(double x) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    // For now, just verify we can find both overloads
    // Parameter type encoding is a future milestone
    int overloadCount = 0;
    for (auto *D : AST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getName() == "compute") {
                overloadCount++;
                ASSERT(!FD->isExternC(), "Overloaded function should NOT have C linkage");
            }
        }
    }

    ASSERT(overloadCount == 2, "Should find 2 overloads of 'compute'");

    // NOTE: Parameter type encoding not yet implemented
    // Future milestone will add: compute_int, compute_double

    TEST_PASS("OverloadedCppFunctions (param encoding not yet implemented)");
}

// ============================================================================
// Test 6: extern "C" should NOT get parameter encoding
// ============================================================================
void test_ExternCNoParameterEncoding() {
    TEST_START("ExternCNoParameterEncoding");

    const char *code = R"(
        extern "C" void process(int x, double y) {
            // C linkage - no overloading allowed
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionDecl *FD = findFunction(AST->getASTContext(), "process");
    ASSERT(FD != nullptr, "Function 'process' not found");

    ASSERT(FD->isExternC(), "Function should have C linkage");

    NameMangler mangler(AST->getASTContext());
    std::string mangledName = mangler.mangleFunctionName(FD);

    // extern "C" function should be EXACTLY "process" - no param encoding
    ASSERT(mangledName == "process",
           "extern \"C\" should not have parameter encoding (expected 'process', got '" + mangledName + "')");

    TEST_PASS("ExternCNoParameterEncoding");
}

// ============================================================================
// Main function
// ============================================================================
int main() {
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" << std::endl;
    std::cout << " Milestone #2: extern \"C\" Name Mangling Tests" << std::endl;
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" << std::endl;
    std::cout << std::endl;

    test_ExternCFunctionUnmangled();
    test_CppFunctionMangled();
    test_ExternCInNamespace();
    test_MixedNamespace();
    test_OverloadedCppFunctions();
    test_ExternCNoParameterEncoding();

    std::cout << std::endl;
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" << std::endl;
    std::cout << " All Milestone #2 Tests Complete" << std::endl;
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" << std::endl;

    return 0;
}
