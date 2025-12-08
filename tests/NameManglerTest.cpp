// TDD Tests for NameMangler - Epic #3 Implementation
// Story #18: Basic name mangling

#include "NameMangler.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include <iostream>

using namespace clang;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Helper to build AST and find method
CXXMethodDecl* findMethod(ASTUnit *AST, const std::string &className, const std::string &methodName) {
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    for (auto *Decl : TU->decls()) {
        if (auto *CXXRecord = dyn_cast<CXXRecordDecl>(Decl)) {
            if (CXXRecord->getName() == className) {
                for (auto *Method : CXXRecord->methods()) {
                    if (Method->getName() == methodName) {
                        return Method;
                    }
                }
            }
        }
    }
    return nullptr;
}

CXXConstructorDecl* findConstructor(ASTUnit *AST, const std::string &className) {
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    for (auto *Decl : TU->decls()) {
        if (auto *CXXRecord = dyn_cast<CXXRecordDecl>(Decl)) {
            if (CXXRecord->getName() == className) {
                for (auto *Ctor : CXXRecord->ctors()) {
                    if (!Ctor->isImplicit()) {
                        return Ctor;
                    }
                }
            }
        }
    }
    return nullptr;
}

// ============================================================================
// Story #18: Name Mangling Tests
// ============================================================================

void test_SimpleMethod(ASTContext &Ctx) {
    TEST_START("SimpleMethod: Point::getX() -> Point_getX");

    const char *cpp = R"(
        class Point {
        public:
            int getX();
        };
    )";
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    NameMangler mangler(AST->getASTContext());
    CXXMethodDecl *MD = findMethod(AST.get(), "Point", "getX");
    ASSERT(MD != nullptr, "Method not found");

    std::string mangled = mangler.mangleName(MD);
    ASSERT(mangled == "Point_getX", "Expected Point_getX, got: " + mangled);

    TEST_PASS("SimpleMethod");
}

void test_OverloadedMethods(ASTContext &Ctx) {
    TEST_START("OverloadedMethods: Math::add(int,int) and Math::add(float,float)");

    const char *cpp = R"(
        class Math {
        public:
            int add(int a, int b);
            float add(float a, float b);
        };
    )";
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    NameMangler mangler(AST->getASTContext());

    // Find both methods
    CXXMethodDecl *MD1 = nullptr;
    CXXMethodDecl *MD2 = nullptr;

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    for (auto *Decl : TU->decls()) {
        if (auto *CXXRecord = dyn_cast<CXXRecordDecl>(Decl)) {
            if (CXXRecord->getName() == "Math") {
                for (auto *Method : CXXRecord->methods()) {
                    if (Method->getName() == "add") {
                        if (Method->param_size() > 0) {
                            auto ParamType = Method->getParamDecl(0)->getType();
                            if (ParamType->isIntegerType()) {
                                MD1 = Method;
                            } else if (ParamType->isFloatingType()) {
                                MD2 = Method;
                            }
                        }
                    }
                }
            }
        }
    }

    ASSERT(MD1 != nullptr && MD2 != nullptr, "Methods not found");

    std::string mangled1 = mangler.mangleName(MD1);
    std::string mangled2 = mangler.mangleName(MD2);

    // Names must be different
    ASSERT(mangled1 != mangled2, "Overloaded methods must have different names");

    // Should contain base name
    ASSERT(mangled1.find("Math_add") != std::string::npos, "Should contain Math_add");
    ASSERT(mangled2.find("Math_add") != std::string::npos, "Should contain Math_add");

    TEST_PASS("OverloadedMethods");
}

void test_Constructor(ASTContext &Ctx) {
    TEST_START("Constructor: Point::Point(int,int) -> Point__ctor");

    const char *cpp = R"(
        class Point {
        public:
            Point(int x, int y);
        };
    )";
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    NameMangler mangler(AST->getASTContext());
    CXXConstructorDecl *CD = findConstructor(AST.get(), "Point");
    ASSERT(CD != nullptr, "Constructor not found");

    std::string mangled = mangler.mangleConstructor(CD);
    ASSERT(mangled == "Point__ctor", "Expected Point__ctor, got: " + mangled);

    TEST_PASS("Constructor");
}

void test_UniquenessCheck(ASTContext &Ctx) {
    TEST_START("UniquenessCheck: Multiple calls generate unique names");

    const char *cpp = R"(
        class Test {
        public:
            void foo();
            void bar();
        };
    )";
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    NameMangler mangler(AST->getASTContext());

    CXXMethodDecl *MD1 = findMethod(AST.get(), "Test", "foo");
    CXXMethodDecl *MD2 = findMethod(AST.get(), "Test", "bar");
    ASSERT(MD1 != nullptr && MD2 != nullptr, "Methods not found");

    std::string mangled1 = mangler.mangleName(MD1);
    std::string mangled2 = mangler.mangleName(MD2);

    // Names must be unique
    ASSERT(mangled1 != mangled2, "Different methods must have different names");
    ASSERT(mangled1 == "Test_foo", "Expected Test_foo");
    ASSERT(mangled2 == "Test_bar", "Expected Test_bar");

    TEST_PASS("UniquenessCheck");
}

int main(int argc, const char **argv) {
    // Create a simple test AST for context
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode("int main() { return 0; }");
    if (!AST) {
        std::cerr << "Failed to create test AST" << std::endl;
        return 1;
    }

    ASTContext &Ctx = AST->getASTContext();

    std::cout << "=== Story #18: Basic Name Mangling Tests ===" << std::endl;

    test_SimpleMethod(Ctx);
    test_OverloadedMethods(Ctx);
    test_Constructor(Ctx);
    test_UniquenessCheck(Ctx);

    std::cout << "\n========================================" << std::endl;
    std::cout << "Tests passed: " << tests_passed << std::endl;
    std::cout << "Tests failed: " << tests_failed << std::endl;

    if (tests_failed == 0) {
        std::cout << "\n✓ All tests passed!" << std::endl;
        return 0;
    } else {
        std::cout << "\n✗ Some tests failed!" << std::endl;
        return 1;
    }
}
