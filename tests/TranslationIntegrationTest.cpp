// Integration Tests for Complete C++ to C Translation (Story #20)
// Tests full end-to-end translation of C++ classes to C structs + functions
// Migrated to Google Test

#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "FileOriginTracker.h"
#include "TargetContext.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <iostream>

using namespace clang;

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// Helper to create CppToCVisitor with all required components
std::unique_ptr<CppToCVisitor> createVisitor(ASTUnit &AST, CNodeBuilder &builder,
                                               cpptoc::FileOriginTracker &tracker) {
    TargetContext& targetCtx = TargetContext::getInstance();
    return std::make_unique<CppToCVisitor>(AST.getASTContext(), builder,
                                            targetCtx, tracker, nullptr);
}

// ============================================================================
// Story #20: Translation Integration Tests
// ============================================================================

TEST(TranslationIntegrationTest, EmptyClass) {
    const char *cpp = "class Empty {};";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    auto visitor = createVisitor(*AST, builder, tracker);

    // Run visitor on entire AST
    visitor->TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct Empty {}; generated
    RecordDecl *RD = visitor->getCStruct("Empty");
    ASSERT_NE(RD, nullptr) << "Struct not generated";
    EXPECT_EQ(RD->getName(), "Empty") << "Struct name mismatch";

    // Validate: no fields
    int fieldCount = 0;
    for (auto *Field : RD->fields()) {
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 0) << "Empty class should have no fields";
}

TEST(TranslationIntegrationTest, SimpleClassWithMethod) {
    const char *cpp = R"(
        class Point {
            int x, y;
        public:
            int getX() { return x; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    auto visitor = createVisitor(*AST, builder, tracker);

    visitor->TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct Point with 2 fields generated
    RecordDecl *RD = visitor->getCStruct("Point");
    ASSERT_NE(RD, nullptr) << "Struct not generated";

    int fieldCount = 0;
    for (auto *Field : RD->fields()) {
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 2) << "Expected 2 fields";

    // Validate: Point_getX function generated
    FunctionDecl *FD = visitor->getCFunc("Point_getX");
    ASSERT_NE(FD, nullptr) << "Method function not generated";
    EXPECT_EQ(FD->getNumParams(), 1) << "Expected 1 parameter (this)";

    // Validate: function has body
    Stmt *Body = FD->getBody();
    EXPECT_NE(Body, nullptr) << "Function body not translated";
}

TEST(TranslationIntegrationTest, ConstructorTranslation) {
    const char *cpp = R"(
        class Point {
            int x, y;
        public:
            Point(int x, int y) : x(x), y(y) {}
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    auto visitor = createVisitor(*AST, builder, tracker);

    visitor->TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct generated
    RecordDecl *RD = visitor->getCStruct("Point");
    ASSERT_NE(RD, nullptr) << "Struct not generated";

    // Validate: constructor function generated
    FunctionDecl *FD = visitor->getCtor("Point__ctor");
    ASSERT_NE(FD, nullptr) << "Constructor function not generated";
    EXPECT_EQ(FD->getNumParams(), 3) << "Expected 3 parameters (this + 2 params)";
    EXPECT_TRUE(FD->getReturnType()->isVoidType()) << "Constructor should return void";

    // Validate: function has body with assignments
    Stmt *Body = FD->getBody();
    EXPECT_NE(Body, nullptr) << "Constructor body not translated";
}

TEST(TranslationIntegrationTest, OverloadedMethods) {
    const char *cpp = R"(
        class Math {
        public:
            int add(int a, int b) { return a + b; }
            float add(float a, float b) { return a + b; }
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    auto visitor = createVisitor(*AST, builder, tracker);

    visitor->TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct generated
    RecordDecl *RD = visitor->getCStruct("Math");
    ASSERT_NE(RD, nullptr) << "Struct not generated";

    // Validate: both add methods have unique names
    FunctionDecl *FD1 = visitor->getCFunc("Math_add");
    EXPECT_NE(FD1, nullptr) << "First add method not generated";

    // Second one should have type suffix
    FunctionDecl *FD2 = visitor->getCFunc("Math_add_float_float");
    EXPECT_NE(FD2, nullptr) << "Second add method not generated with unique name";
}

TEST(TranslationIntegrationTest, ComplexClass) {
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
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    auto visitor = createVisitor(*AST, builder, tracker);

    visitor->TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: struct with 2 fields
    RecordDecl *RD = visitor->getCStruct("Rectangle");
    ASSERT_NE(RD, nullptr) << "Struct not generated";

    int fieldCount = 0;
    for (auto *Field : RD->fields()) {
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 2) << "Expected 2 fields";

    // Validate: constructor generated
    FunctionDecl *Ctor = visitor->getCtor("Rectangle__ctor");
    ASSERT_NE(Ctor, nullptr) << "Constructor not generated";
    EXPECT_EQ(Ctor->getNumParams(), 3) << "Expected 3 params (this + 2)";

    // Validate: 3 methods generated
    FunctionDecl *GetWidth = visitor->getCFunc("Rectangle_getWidth");
    EXPECT_NE(GetWidth, nullptr) << "getWidth method not generated";

    FunctionDecl *GetHeight = visitor->getCFunc("Rectangle_getHeight");
    EXPECT_NE(GetHeight, nullptr) << "getHeight method not generated";

    FunctionDecl *Area = visitor->getCFunc("Rectangle_area");
    EXPECT_NE(Area, nullptr) << "area method not generated";

    // Validate: all functions have bodies
    EXPECT_NE(Ctor->getBody(), nullptr) << "Constructor body missing";
    EXPECT_NE(GetWidth->getBody(), nullptr) << "getWidth body missing";
    EXPECT_NE(GetHeight->getBody(), nullptr) << "getHeight body missing";
    EXPECT_NE(Area->getBody(), nullptr) << "area body missing";
}

TEST(TranslationIntegrationTest, MultipleClasses) {
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
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    auto visitor = createVisitor(*AST, builder, tracker);

    visitor->TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Validate: both structs generated
    RecordDecl *Point = visitor->getCStruct("Point");
    EXPECT_NE(Point, nullptr) << "Point struct not generated";

    RecordDecl *Circle = visitor->getCStruct("Circle");
    EXPECT_NE(Circle, nullptr) << "Circle struct not generated";

    // Validate: both constructors generated
    FunctionDecl *PointCtor = visitor->getCtor("Point__ctor");
    EXPECT_NE(PointCtor, nullptr) << "Point constructor not generated";

    FunctionDecl *CircleCtor = visitor->getCtor("Circle__ctor");
    EXPECT_NE(CircleCtor, nullptr) << "Circle constructor not generated";

    // Validate: both methods generated
    FunctionDecl *GetX = visitor->getCFunc("Point_getX");
    EXPECT_NE(GetX, nullptr) << "Point::getX not generated";

    FunctionDecl *GetRadius = visitor->getCFunc("Circle_getRadius");
    EXPECT_NE(GetRadius, nullptr) << "Circle::getRadius not generated";
}
