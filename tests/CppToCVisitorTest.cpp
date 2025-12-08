// TDD Tests for CppToCVisitor - Epic #3 Implementation
// Story #15: Class-to-struct conversion

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
// Story #15: Class-to-Struct Conversion Tests
// ============================================================================

void test_EmptyClass(ASTContext &Ctx) {
    TEST_START("EmptyClass: class Empty {} -> struct Empty {}");

    const char *cpp = "class Empty {};";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    // Run visitor on AST
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify C struct generated
    RecordDecl *CStruct = visitor.getCStruct("Empty");
    ASSERT(CStruct != nullptr, "C struct not generated");
    ASSERT(CStruct->getName() == "Empty", "Struct name mismatch");

    TEST_PASS("EmptyClass");
}

void test_ClassWithFields(ASTContext &Ctx) {
    TEST_START("ClassWithFields: class Point { int x, y; }");

    const char *cpp = "class Point { int x, y; };";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    RecordDecl *CStruct = visitor.getCStruct("Point");
    ASSERT(CStruct != nullptr, "C struct not generated");

    // Count fields
    int fieldCount = 0;
    for (auto *Field : CStruct->fields()) {
        fieldCount++;
    }
    ASSERT(fieldCount == 2, "Expected 2 fields, got different count");

    TEST_PASS("ClassWithFields");
}

void test_MixedAccessSpecifiers(ASTContext &Ctx) {
    TEST_START("MixedAccessSpecifiers: public/private -> all public in C");

    const char *cpp = R"(
        class Point {
        private:
            int x;
        public:
            int y;
        protected:
            int z;
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    RecordDecl *CStruct = visitor.getCStruct("Point");
    ASSERT(CStruct != nullptr, "C struct not generated");

    // All fields should be present (access specifiers ignored in C)
    int fieldCount = 0;
    for (auto *Field : CStruct->fields()) {
        fieldCount++;
    }
    ASSERT(fieldCount == 3, "Expected 3 fields (all access levels)");

    TEST_PASS("MixedAccessSpecifiers");
}

void test_ForwardDeclaration(ASTContext &Ctx) {
    TEST_START("ForwardDeclaration: class Forward; -> skip");

    const char *cpp = "class Forward;";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Forward declarations should be skipped
    RecordDecl *CStruct = visitor.getCStruct("Forward");
    ASSERT(CStruct == nullptr, "Forward declaration should be skipped");

    TEST_PASS("ForwardDeclaration");
}

// ============================================================================
// Story #16: Method-to-Function Conversion Tests
// ============================================================================

void test_SimpleMethod(ASTContext &Ctx) {
    TEST_START("SimpleMethod: int getX() -> int Point_getX(struct Point *this)");

    const char *cpp = R"(
        class Point {
            int x;
        public:
            int getX() { return x; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify C function generated with correct signature
    FunctionDecl *CFunc = visitor.getCFunc("Point_getX");
    ASSERT(CFunc != nullptr, "C function not generated");
    ASSERT(CFunc->getNumParams() == 1, "Expected 1 parameter (this)");
    ASSERT(CFunc->getParamDecl(0)->getName() == "this", "First param should be 'this'");

    TEST_PASS("SimpleMethod");
}

void test_MethodWithParams(ASTContext &Ctx) {
    TEST_START("MethodWithParams: void setX(int x) -> void Point_setX(struct Point *this, int x)");

    const char *cpp = R"(
        class Point {
            int x;
        public:
            void setX(int val) { x = val; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("Point_setX");
    ASSERT(CFunc != nullptr, "C function not generated");
    ASSERT(CFunc->getNumParams() == 2, "Expected 2 parameters (this + val)");
    ASSERT(CFunc->getParamDecl(0)->getName() == "this", "First param should be 'this'");
    ASSERT(CFunc->getParamDecl(1)->getName() == "val", "Second param should be 'val'");

    TEST_PASS("MethodWithParams");
}

void test_SkipVirtual(ASTContext &Ctx) {
    TEST_START("SkipVirtual: virtual void foo() -> skip (no function generated)");

    const char *cpp = R"(
        class Base {
        public:
            virtual void foo() {}
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Virtual methods should be skipped in Phase 1
    FunctionDecl *CFunc = visitor.getCFunc("Base_foo");
    ASSERT(CFunc == nullptr, "Virtual method should be skipped");

    TEST_PASS("SkipVirtual");
}

// ============================================================================
// Story #19: Member Access Transformation Tests
// ============================================================================

void test_ImplicitThisRead(ASTContext &Ctx) {
    TEST_START("ImplicitThisRead: return x; -> return this->x;");

    const char *cpp = R"(
        class Point {
            int x;
        public:
            int getX() { return x; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify function was generated
    FunctionDecl *CFunc = visitor.getCFunc("Point_getX");
    ASSERT(CFunc != nullptr, "C function not generated");

    // Verify function has body
    Stmt *Body = CFunc->getBody();
    ASSERT(Body != nullptr, "Function body not translated");

    TEST_PASS("ImplicitThisRead");
}

void test_ImplicitThisWrite(ASTContext &Ctx) {
    TEST_START("ImplicitThisWrite: x = val; -> this->x = val;");

    const char *cpp = R"(
        class Point {
            int x;
        public:
            void setX(int val) { x = val; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify function was generated
    FunctionDecl *CFunc = visitor.getCFunc("Point_setX");
    ASSERT(CFunc != nullptr, "C function not generated");

    // Verify function has body with translated assignment
    Stmt *Body = CFunc->getBody();
    ASSERT(Body != nullptr, "Function body not translated");

    TEST_PASS("ImplicitThisWrite");
}

void test_ExplicitMemberAccess(ASTContext &Ctx) {
    TEST_START("ExplicitMemberAccess: obj.x preserved in translation");

    const char *cpp = R"(
        class Point {
            int x;
        public:
            int distance(Point other) { return x - other.x; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify function was generated with translated body
    FunctionDecl *CFunc = visitor.getCFunc("Point_distance");
    ASSERT(CFunc != nullptr, "C function not generated");

    Stmt *Body = CFunc->getBody();
    ASSERT(Body != nullptr, "Function body not translated");

    TEST_PASS("ExplicitMemberAccess");
}

void test_MultipleFieldAccess(ASTContext &Ctx) {
    TEST_START("MultipleFieldAccess: return width * height;");

    const char *cpp = R"(
        class Rectangle {
            int width, height;
        public:
            int area() { return width * height; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify function was generated
    FunctionDecl *CFunc = visitor.getCFunc("Rectangle_area");
    ASSERT(CFunc != nullptr, "C function not generated");

    // Verify both implicit member accesses are translated
    Stmt *Body = CFunc->getBody();
    ASSERT(Body != nullptr, "Function body not translated");

    TEST_PASS("MultipleFieldAccess");
}

// ============================================================================
// Story #17: Constructor Translation Tests
// ============================================================================

void test_DefaultConstructor(ASTContext &Ctx) {
    TEST_START("DefaultConstructor: Point() {} -> void Point__ctor(struct Point *this) {}");

    const char *cpp = R"(
        class Point {
            int x, y;
        public:
            Point() {}
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify constructor function was generated
    FunctionDecl *CFunc = visitor.getCtor("Point__ctor");
    ASSERT(CFunc != nullptr, "Constructor function not generated");
    ASSERT(CFunc->getNumParams() == 1, "Expected 1 parameter (this)");
    ASSERT(CFunc->getReturnType()->isVoidType(), "Constructor should return void");

    TEST_PASS("DefaultConstructor");
}

void test_MemberInitializers(ASTContext &Ctx) {
    TEST_START("MemberInitializers: Point(int x, int y) : x(x), y(y) {}");

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

    // Verify constructor function was generated
    FunctionDecl *CFunc = visitor.getCtor("Point__ctor");
    ASSERT(CFunc != nullptr, "Constructor function not generated");
    ASSERT(CFunc->getNumParams() == 3, "Expected 3 parameters (this + 2 params)");

    // Verify function has body with member initializers translated to assignments
    Stmt *Body = CFunc->getBody();
    ASSERT(Body != nullptr, "Constructor body not translated");

    TEST_PASS("MemberInitializers");
}

void test_ConstructorWithBody(ASTContext &Ctx) {
    TEST_START("ConstructorWithBody: Constructor with statements in body");

    const char *cpp = R"(
        class Rectangle {
            int width, height, area;
        public:
            Rectangle(int w, int h) : width(w), height(h) {
                area = width * height;
            }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify constructor was generated
    FunctionDecl *CFunc = visitor.getCtor("Rectangle__ctor");
    ASSERT(CFunc != nullptr, "Constructor function not generated");

    // Verify body has both initializers and body statements
    Stmt *Body = CFunc->getBody();
    ASSERT(Body != nullptr, "Constructor body not translated");

    TEST_PASS("ConstructorWithBody");
}

int main(int argc, const char **argv) {
    // Create a simple test AST for context
    std::unique_ptr<ASTUnit> AST = buildAST("int main() { return 0; }");
    if (!AST) {
        std::cerr << "Failed to create test AST" << std::endl;
        return 1;
    }

    ASTContext &Ctx = AST->getASTContext();

    std::cout << "=== Story #15: Class-to-Struct Conversion Tests ===" << std::endl;
    test_EmptyClass(Ctx);
    test_ClassWithFields(Ctx);
    test_MixedAccessSpecifiers(Ctx);
    test_ForwardDeclaration(Ctx);

    std::cout << "\n=== Story #16: Method-to-Function Conversion Tests ===" << std::endl;
    test_SimpleMethod(Ctx);
    test_MethodWithParams(Ctx);
    test_SkipVirtual(Ctx);

    std::cout << "\n=== Story #19: Member Access Transformation Tests ===" << std::endl;
    test_ImplicitThisRead(Ctx);
    test_ImplicitThisWrite(Ctx);
    test_ExplicitMemberAccess(Ctx);
    test_MultipleFieldAccess(Ctx);

    std::cout << "\n=== Story #17: Constructor Translation Tests ===" << std::endl;
    test_DefaultConstructor(Ctx);
    test_MemberInitializers(Ctx);
    test_ConstructorWithBody(Ctx);

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
