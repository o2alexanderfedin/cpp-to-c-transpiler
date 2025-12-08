// Integration Tests for Complete C++ to C Translation (Story #20)
// Tests full end-to-end translation of C++ classes to C structs + functions

#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>

using namespace clang;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// ============================================================================
// Story #20: Translation Integration Tests
// ============================================================================

void test_EmptyClass(ASTContext &Ctx) {
    TEST_START("EmptyClass: Full translation of empty class");

    const char *cpp = "class Empty {};";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    // Run visitor on entire AST
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct Empty {}; generated
    RecordDecl *RD = visitor.getCStruct("Empty");
    ASSERT(RD != nullptr, "Struct not generated");
    ASSERT(RD->getName() == "Empty", "Struct name mismatch");

    // Validate: no fields
    int fieldCount = 0;
    for (auto *Field : RD->fields()) {
        fieldCount++;
    }
    ASSERT(fieldCount == 0, "Empty class should have no fields");

    TEST_PASS("EmptyClass");
}

void test_SimpleClassWithMethod(ASTContext &Ctx) {
    TEST_START("SimpleClassWithMethod: Class with one getter method");

    const char *cpp = R"(
        class Point {
            int x, y;
        public:
            int getX() { return x; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct Point with 2 fields generated
    RecordDecl *RD = visitor.getCStruct("Point");
    ASSERT(RD != nullptr, "Struct not generated");

    int fieldCount = 0;
    for (auto *Field : RD->fields()) {
        fieldCount++;
    }
    ASSERT(fieldCount == 2, "Expected 2 fields");

    // Validate: Point_getX function generated
    FunctionDecl *FD = visitor.getCFunc("Point_getX");
    ASSERT(FD != nullptr, "Method function not generated");
    ASSERT(FD->getNumParams() == 1, "Expected 1 parameter (this)");

    // Validate: function has body
    Stmt *Body = FD->getBody();
    ASSERT(Body != nullptr, "Function body not translated");

    TEST_PASS("SimpleClassWithMethod");
}

void test_ConstructorTranslation(ASTContext &Ctx) {
    TEST_START("ConstructorTranslation: Class with constructor and member initializers");

    const char *cpp = R"(
        class Point {
            int x, y;
        public:
            Point(int x, int y) : x(x), y(y) {}
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct generated
    RecordDecl *RD = visitor.getCStruct("Point");
    ASSERT(RD != nullptr, "Struct not generated");

    // Validate: constructor function generated
    FunctionDecl *FD = visitor.getCtor("Point__ctor");
    ASSERT(FD != nullptr, "Constructor function not generated");
    ASSERT(FD->getNumParams() == 3, "Expected 3 parameters (this + 2 params)");
    ASSERT(FD->getReturnType()->isVoidType(), "Constructor should return void");

    // Validate: function has body with assignments
    Stmt *Body = FD->getBody();
    ASSERT(Body != nullptr, "Constructor body not translated");

    TEST_PASS("ConstructorTranslation");
}

void test_OverloadedMethods(ASTContext &Ctx) {
    TEST_START("OverloadedMethods: Class with overloaded methods -> unique C names");

    const char *cpp = R"(
        class Math {
        public:
            int add(int a, int b) { return a + b; }
            float add(float a, float b) { return a + b; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct generated
    RecordDecl *RD = visitor.getCStruct("Math");
    ASSERT(RD != nullptr, "Struct not generated");

    // Validate: both add methods have unique names
    // First one should be Math_add (no suffix needed)
    FunctionDecl *FD1 = visitor.getCFunc("Math_add");
    ASSERT(FD1 != nullptr, "First add method not generated");

    // Second one should have type suffix
    FunctionDecl *FD2 = visitor.getCFunc("Math_add_float_float");
    ASSERT(FD2 != nullptr, "Second add method not generated with unique name");

    TEST_PASS("OverloadedMethods");
}

void test_ComplexClass(ASTContext &Ctx) {
    TEST_START("ComplexClass: Rectangle with constructor + 3 methods");

    const char *cpp = R"(
        class Rectangle {
            int width, height;
        public:
            Rectangle(int w, int h) : width(w), height(h) {}
            int getWidth() { return width; }
            int getHeight() { return height; }
            int area() { return width * height; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct with 2 fields
    RecordDecl *RD = visitor.getCStruct("Rectangle");
    ASSERT(RD != nullptr, "Struct not generated");

    int fieldCount = 0;
    for (auto *Field : RD->fields()) {
        fieldCount++;
    }
    ASSERT(fieldCount == 2, "Expected 2 fields");

    // Validate: constructor generated
    FunctionDecl *Ctor = visitor.getCtor("Rectangle__ctor");
    ASSERT(Ctor != nullptr, "Constructor not generated");
    ASSERT(Ctor->getNumParams() == 3, "Expected 3 params (this + 2)");

    // Validate: 3 methods generated
    FunctionDecl *GetWidth = visitor.getCFunc("Rectangle_getWidth");
    ASSERT(GetWidth != nullptr, "getWidth method not generated");

    FunctionDecl *GetHeight = visitor.getCFunc("Rectangle_getHeight");
    ASSERT(GetHeight != nullptr, "getHeight method not generated");

    FunctionDecl *Area = visitor.getCFunc("Rectangle_area");
    ASSERT(Area != nullptr, "area method not generated");

    // Validate: all functions have bodies
    ASSERT(Ctor->getBody() != nullptr, "Constructor body missing");
    ASSERT(GetWidth->getBody() != nullptr, "getWidth body missing");
    ASSERT(GetHeight->getBody() != nullptr, "getHeight body missing");
    ASSERT(Area->getBody() != nullptr, "area body missing");

    TEST_PASS("ComplexClass");
}

void test_MultipleClasses(ASTContext &Ctx) {
    TEST_START("MultipleClasses: Multiple classes in one translation unit");

    const char *cpp = R"(
        class Point {
            int x, y;
        public:
            Point(int x, int y) : x(x), y(y) {}
            int getX() { return x; }
        };

        class Circle {
            int radius;
        public:
            Circle(int r) : radius(r) {}
            int getRadius() { return radius; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: both structs generated
    RecordDecl *Point = visitor.getCStruct("Point");
    ASSERT(Point != nullptr, "Point struct not generated");

    RecordDecl *Circle = visitor.getCStruct("Circle");
    ASSERT(Circle != nullptr, "Circle struct not generated");

    // Validate: both constructors generated
    FunctionDecl *PointCtor = visitor.getCtor("Point__ctor");
    ASSERT(PointCtor != nullptr, "Point constructor not generated");

    FunctionDecl *CircleCtor = visitor.getCtor("Circle__ctor");
    ASSERT(CircleCtor != nullptr, "Circle constructor not generated");

    // Validate: both methods generated
    FunctionDecl *GetX = visitor.getCFunc("Point_getX");
    ASSERT(GetX != nullptr, "Point::getX not generated");

    FunctionDecl *GetRadius = visitor.getCFunc("Circle_getRadius");
    ASSERT(GetRadius != nullptr, "Circle::getRadius not generated");

    TEST_PASS("MultipleClasses");
}

int main(int argc, const char **argv) {
    // Create a simple test AST for context
    std::unique_ptr<ASTUnit> AST = buildAST("int main() { return 0; }");
    if (!AST) {
        std::cerr << "Failed to create test AST" << std::endl;
        return 1;
    }

    ASTContext &Ctx = AST->getASTContext();

    std::cout << "=== Story #20: Translation Integration Tests ===" << std::endl;
    test_EmptyClass(Ctx);
    test_SimpleClassWithMethod(Ctx);
    test_ConstructorTranslation(Ctx);
    test_OverloadedMethods(Ctx);
    test_ComplexClass(Ctx);
    test_MultipleClasses(Ctx);

    std::cout << "\n========================================" << std::endl;
    std::cout << "Tests passed: " << tests_passed << std::endl;
    std::cout << "Tests failed: " << tests_failed << std::endl;

    if (tests_failed == 0) {
        std::cout << "\n✓ All integration tests passed!" << std::endl;
        std::cout << "✓ Epic #3 Complete: Simple Class Translation works end-to-end!" << std::endl;
        return 0;
    } else {
        std::cout << "\n✗ Some tests failed!" << std::endl;
        return 1;
    }
}
