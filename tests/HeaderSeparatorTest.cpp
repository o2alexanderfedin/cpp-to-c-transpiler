// TDD Tests for HeaderSeparator - Epic #19 Implementation
// Story #137: Header/Implementation Separation

#include "HeaderSeparator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/Decl.h"
#include <iostream>

using namespace clang;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Test 1: Simple struct routes to header only
void test_CompleteStructGoesToHeader() {
    TEST_START("CompleteStructGoesToHeader");

    // Arrange
    const char *Code = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    // Act
    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Assert
    ASSERT(separator.getHeaderDecls().size() == 1,
           "Expected 1 header declaration");
    ASSERT(separator.getImplDecls().size() == 0,
           "Expected 0 implementation declarations");

    auto *FirstDecl = separator.getHeaderDecls()[0];
    ASSERT(llvm::isa<clang::RecordDecl>(FirstDecl),
           "Expected RecordDecl type");
    ASSERT(llvm::cast<clang::RecordDecl>(FirstDecl)->getName() == "Point",
           "Expected struct name to be 'Point'");

    TEST_PASS("CompleteStructGoesToHeader");
}

// Test 2: Function declaration routes to header
void test_FunctionDeclarationGoesToHeader() {
    TEST_START("FunctionDeclarationGoesToHeader");

    const char *Code = R"(
        void myFunction(int x);
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    ASSERT(separator.getHeaderDecls().size() == 1,
           "Expected 1 header declaration");
    ASSERT(separator.getImplDecls().size() == 0,
           "Expected 0 implementation declarations");

    auto *FirstDecl = separator.getHeaderDecls()[0];
    ASSERT(llvm::isa<clang::FunctionDecl>(FirstDecl),
           "Expected FunctionDecl type");
    ASSERT(llvm::cast<clang::FunctionDecl>(FirstDecl)->getName() == "myFunction",
           "Expected function name to be 'myFunction'");

    TEST_PASS("FunctionDeclarationGoesToHeader");
}

// Test 3: Function definition goes to implementation AND header (for declaration)
void test_FunctionDefinitionGoesToBoth() {
    TEST_START("FunctionDefinitionGoesToBoth");

    const char *Code = R"(
        void myFunction(int x) {
            // function body
        }
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Definition goes to impl
    ASSERT(separator.getImplDecls().size() == 1,
           "Expected 1 implementation declaration");

    // Declaration also goes to header (same FunctionDecl, will be printed differently)
    ASSERT(separator.getHeaderDecls().size() == 1,
           "Expected 1 header declaration");

    // Both should reference the same function
    auto *ImplDecl = llvm::cast<clang::FunctionDecl>(separator.getImplDecls()[0]);
    auto *HeaderDecl = llvm::cast<clang::FunctionDecl>(separator.getHeaderDecls()[0]);

    ASSERT(ImplDecl->hasBody(),
           "Implementation declaration should have body");
    ASSERT(ImplDecl->getName() == "myFunction",
           "Expected function name to be 'myFunction'");

    TEST_PASS("FunctionDefinitionGoesToBoth");
}

// Test 4: Class with methods (integration test)
void test_ClassWithMethods() {
    TEST_START("ClassWithMethods");

    const char *Code = R"(
        class MyClass {
            int x;
        public:
            MyClass(int x);
            int getX() const;
        };

        MyClass::MyClass(int x) : x(x) {}
        int MyClass::getX() const { return x; }
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Clang creates FunctionDecl nodes for:
    // - In-class method declarations (constructor/getX prototypes in class)
    // - Out-of-line method definitions (constructor/getX implementations)
    //
    // Header will contain: RecordDecl + all FunctionDecls (as declarations)
    // Impl will contain: FunctionDecls with bodies (in-class implicit + out-of-line)
    //
    // Expected counts: Header: 5 (1 class + 4 methods), Impl: 4 (methods with bodies)

    ASSERT(separator.getHeaderDecls().size() == 5,
           "Expected 5 header declarations (1 class + 4 method declarations)");

    ASSERT(separator.getImplDecls().size() == 4,
           "Expected 4 implementation declarations (4 methods with bodies)");

    TEST_PASS("ClassWithMethods");
}

// Test 5: Empty translation unit (edge case)
void test_EmptyTranslationUnit() {
    TEST_START("EmptyTranslationUnit");

    const char *Code = "";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Empty TU → empty lists
    ASSERT(separator.getHeaderDecls().size() == 0,
           "Expected 0 header declarations");
    ASSERT(separator.getImplDecls().size() == 0,
           "Expected 0 implementation declarations");

    TEST_PASS("EmptyTranslationUnit");
}

// Test 6: Multiple classes
void test_MultipleClasses() {
    TEST_START("MultipleClasses");

    const char *Code = R"(
        struct Point {
            int x, y;
        };

        struct Circle {
            Point center;
            double radius;
        };

        struct Rectangle {
            Point topLeft;
            Point bottomRight;
        };
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // All 3 structs should go to header
    ASSERT(separator.getHeaderDecls().size() == 3,
           "Expected 3 header declarations (Point, Circle, Rectangle)");
    ASSERT(separator.getImplDecls().size() == 0,
           "Expected 0 implementation declarations");

    TEST_PASS("MultipleClasses");
}

int main() {
    std::cout << "\n=== HeaderSeparator Tests (Story #137) ===\n\n";

    // Run all tests
    test_CompleteStructGoesToHeader();
    test_FunctionDeclarationGoesToHeader();
    test_FunctionDefinitionGoesToBoth();
    test_ClassWithMethods();
    test_EmptyTranslationUnit();
    test_MultipleClasses();

    // Summary
    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << tests_passed << "\n";
    std::cout << "Failed: " << tests_failed << "\n";

    return tests_failed > 0 ? 1 : 0;
}
