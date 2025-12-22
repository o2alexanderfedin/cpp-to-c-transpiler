// TDD Tests for CppToCVisitor - Epic #3 Implementation
// Story #15: Class-to-struct conversion

#include <gtest/gtest.h>
#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// ============================================================================
// Story #15: Class-to-Struct Conversion Tests
// ============================================================================

// Test fixture
class CppToCVisitorTest : public ::testing::Test {
protected:
};

TEST_F(CppToCVisitorTest, EmptyClass) {
    const char *cpp = "class Empty {};";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        // Run visitor on AST
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify C struct generated
        RecordDecl *CStruct = visitor.getCStruct("Empty");
        ASSERT_TRUE(CStruct != nullptr) << "C struct not generated";
        ASSERT_TRUE(CStruct->getName() == "Empty") << "Struct name mismatch";
}

TEST_F(CppToCVisitorTest, ClassWithFields) {
    const char *cpp = "class Point { int x, y; };";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        RecordDecl *CStruct = visitor.getCStruct("Point");
        ASSERT_TRUE(CStruct != nullptr) << "C struct not generated";

        // Count fields
        int fieldCount = 0;
        for (auto *Field : CStruct->fields()) {
            fieldCount++;
        }
        ASSERT_TRUE(fieldCount == 2) << "Expected 2 fields, got different count";
}

TEST_F(CppToCVisitorTest, MixedAccessSpecifiers) {

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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        RecordDecl *CStruct = visitor.getCStruct("Point");
        ASSERT_TRUE(CStruct != nullptr) << "C struct not generated";

        // All fields should be present (access specifiers ignored in C)
        int fieldCount = 0;
        for (auto *Field : CStruct->fields()) {
            fieldCount++;
        }
        ASSERT_TRUE(fieldCount == 3) << "Expected 3 fields (all access levels)";
}

TEST_F(CppToCVisitorTest, ForwardDeclaration) {
    const char *cpp = "class Forward;";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Forward declarations should be skipped
        RecordDecl *CStruct = visitor.getCStruct("Forward");
        ASSERT_TRUE(CStruct == nullptr) << "Forward declaration should be skipped";
}

TEST_F(CppToCVisitorTest, SimpleMethod) {
    const char *cpp = R"(
            class Point {
                int x;
            public:
                int getX() { return x; }
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify C function generated with correct signature
        FunctionDecl *CFunc = visitor.getCFunc("Point_getX");
        ASSERT_TRUE(CFunc != nullptr) << "C function not generated";
        ASSERT_TRUE(CFunc->getNumParams() == 1) << "Expected 1 parameter (this)";
        ASSERT_TRUE(CFunc->getParamDecl(0)->getName() == "this") << "First param should be 'this'";
}

TEST_F(CppToCVisitorTest, MethodWithParams) {
    const char *cpp = R"(
            class Point {
                int x;
            public:
                void setX(int val) { x = val; }
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        FunctionDecl *CFunc = visitor.getCFunc("Point_setX");
        ASSERT_TRUE(CFunc != nullptr) << "C function not generated";
        ASSERT_TRUE(CFunc->getNumParams() == 2) << "Expected 2 parameters (this + val;");
        ASSERT_TRUE(CFunc->getParamDecl(0)->getName() == "this") << "First param should be 'this'";
        ASSERT_TRUE(CFunc->getParamDecl(1)->getName() == "val") << "Second param should be 'val'";
}

TEST_F(CppToCVisitorTest, SkipVirtual) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    -> skip (no function generated)");

        const char *cpp = R"(
            class Base {
            public:
                virtual void foo() {}
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Virtual methods should be skipped in Phase 1
        FunctionDecl *CFunc = visitor.getCFunc("Base_foo");
        ASSERT_TRUE(CFunc == nullptr) << "Virtual method should be skipped";
}

TEST_F(CppToCVisitorTest, ImplicitthisreadReturnXReturnThisX) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    const char *cpp = R"(
            class Point {
                int x;
            public:
                int getX() { return x; }
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify function was generated
        FunctionDecl *CFunc = visitor.getCFunc("Point_getX");
        ASSERT_TRUE(CFunc != nullptr) << "C function not generated";

        // Verify function has body
        Stmt *Body = CFunc->getBody();
        ASSERT_TRUE(Body != nullptr) << "Function body not translated";
}

TEST_F(CppToCVisitorTest, ImplicitthiswriteX=ValThisX=Val) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    const char *cpp = R"(
            class Point {
                int x;
            public:
                void setX(int val) { x = val; }
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify function was generated
        FunctionDecl *CFunc = visitor.getCFunc("Point_setX");
        ASSERT_TRUE(CFunc != nullptr) << "C function not generated";

        // Verify function has body with translated assignment
        Stmt *Body = CFunc->getBody();
        ASSERT_TRUE(Body != nullptr) << "Function body not translated";
}

TEST_F(CppToCVisitorTest, ExplicitmemberaccessObj.xPreservedInTranslation) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    const char *cpp = R"(
            class Point {
                int x;
            public:
                int distance(Point other) { return x - other.x; }
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify function was generated with translated body
        FunctionDecl *CFunc = visitor.getCFunc("Point_distance");
        ASSERT_TRUE(CFunc != nullptr) << "C function not generated";

        Stmt *Body = CFunc->getBody();
        ASSERT_TRUE(Body != nullptr) << "Function body not translated";
}

TEST_F(CppToCVisitorTest, MultiplefieldaccessReturnWidthHeight) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    const char *cpp = R"(
            class Rectangle {
                int width, height;
            public:
                int area() { return width * height; }
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify function was generated
        FunctionDecl *CFunc = visitor.getCFunc("Rectangle_area");
        ASSERT_TRUE(CFunc != nullptr) << "C function not generated";

        // Verify both implicit member accesses are translated
        Stmt *Body = CFunc->getBody();
        ASSERT_TRUE(Body != nullptr) << "Function body not translated";
}

TEST_F(CppToCVisitorTest, DefaultconstructorPointVoidPointCtorStructPointThis)_{}) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    {} -> void Point__ctor(struct Point *this) {}");

        const char *cpp = R"(
            class Point {
                int x, y;
            public:
                Point() {}
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify constructor function was generated
        FunctionDecl *CFunc = visitor.getCtor("Point__ctor");
        ASSERT_TRUE(CFunc != nullptr) << "Constructor function not generated";
        ASSERT_TRUE(CFunc->getNumParams() == 1) << "Expected 1 parameter (this;");
        ASSERT_TRUE(CFunc->getReturnType()->isVoidType()) << "Constructor should return void";
}

TEST_F(CppToCVisitorTest, MemberinitializersPointIntXIntY)_:_x(x),_y(y)_{}) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    : x(x), y(y) {}");

        const char *cpp = R"(
            class Point {
                int x, y;
            public:
                Point(int x, int y) : x(x), y(y) {}
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify constructor function was generated
        FunctionDecl *CFunc = visitor.getCtor("Point__ctor");
        ASSERT_TRUE(CFunc != nullptr) << "Constructor function not generated";
        ASSERT_TRUE(CFunc->getNumParams() == 3) << "Expected 3 parameters (this + 2 params;");

        // Verify function has body with member initializers translated to assignments
        Stmt *Body = CFunc->getBody();
        ASSERT_TRUE(Body != nullptr) << "Constructor body not translated";
}

TEST_F(CppToCVisitorTest, ConstructorwithbodyConstructorWithStatementsInBody) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify constructor was generated
        FunctionDecl *CFunc = visitor.getCtor("Rectangle__ctor");
        ASSERT_TRUE(CFunc != nullptr) << "Constructor function not generated";

        // Verify body has both initializers and body statements
        Stmt *Body = CFunc->getBody();
        ASSERT_TRUE(Body != nullptr) << "Constructor body not translated";
}

TEST_F(CppToCVisitorTest, DestructortranslationDestructorTranslation) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    const char *cpp = R"(
            class Resource {
                int* data;
            public:
                Resource() { data = new int[100]; }
                ~Resource() { delete[] data; }
            };
        )";
        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify destructor function was generated
        FunctionDecl *CDtor = visitor.getDtor("Resource__dtor");
        ASSERT_TRUE(CDtor != nullptr) << "Destructor function not generated";
        ASSERT_TRUE(CDtor->getNumParams() == 1) << "Expected 1 parameter (this;");
        ASSERT_TRUE(CDtor->getReturnType()->isVoidType()) << "Destructor should return void";
}
