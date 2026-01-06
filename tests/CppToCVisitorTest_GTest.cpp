// tests/CppToCVisitorTest_GTest.cpp
// Migrated from CppToCVisitorTest.cpp to Google Test framework
// TDD Tests for CppToCVisitor - Epic #3 Implementation
// Story #15: Class-to-struct conversion

#include <gtest/gtest.h>
#include "CNodeBuilder.h"
#include "FileOriginTracker.h"
#include <clang/AST/ASTContext.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <memory>
#include <string>

using namespace clang;

// Test fixture for CppToCVisitor tests
class CppToCVisitorTestFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// Story #15: Class-to-Struct Conversion Tests
// ============================================================================

TEST_F(CppToCVisitorTestFixture, EmptyClass) {
    const char *cpp = "class Empty {};";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    RecordDecl *CStruct = visitor.getCStruct("Empty");
    ASSERT_NE(CStruct, nullptr) << "C struct not generated";
    EXPECT_EQ(CStruct->getName(), "Empty") << "Struct name mismatch";
}

TEST_F(CppToCVisitorTestFixture, ClassWithFields) {
    const char *cpp = "class Point { int x, y; };";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    RecordDecl *CStruct = visitor.getCStruct("Point");
    ASSERT_NE(CStruct, nullptr) << "C struct not generated";

    int fieldCount = 0;
    for (auto *Field : CStruct->fields()) {
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 2) << "Expected 2 fields";
}

TEST_F(CppToCVisitorTestFixture, MixedAccessSpecifiers) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    RecordDecl *CStruct = visitor.getCStruct("Point");
    ASSERT_NE(CStruct, nullptr) << "C struct not generated";

    int fieldCount = 0;
    for (auto *Field : CStruct->fields()) {
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 3) << "Expected 3 fields (all access levels)";
}

TEST_F(CppToCVisitorTestFixture, ForwardDeclaration) {
    const char *cpp = "class Forward;";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    RecordDecl *CStruct = visitor.getCStruct("Forward");
    EXPECT_EQ(CStruct, nullptr) << "Forward declaration should be skipped";
}

// ============================================================================
// Story #16: Method-to-Function Conversion Tests
// ============================================================================

TEST_F(CppToCVisitorTestFixture, SimpleMethod) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("Point_getX");
    ASSERT_NE(CFunc, nullptr) << "C function not generated";
    EXPECT_EQ(CFunc->getNumParams(), 1u) << "Expected 1 parameter (this)";
    EXPECT_EQ(CFunc->getParamDecl(0)->getName(), "this") << "First param should be 'this'";
}

TEST_F(CppToCVisitorTestFixture, MethodWithParams) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("Point_setX");
    ASSERT_NE(CFunc, nullptr) << "C function not generated";
    EXPECT_EQ(CFunc->getNumParams(), 2u) << "Expected 2 parameters (this + val)";
    EXPECT_EQ(CFunc->getParamDecl(0)->getName(), "this") << "First param should be 'this'";
    EXPECT_EQ(CFunc->getParamDecl(1)->getName(), "val") << "Second param should be 'val'";
}

TEST_F(CppToCVisitorTestFixture, SkipVirtual) {
    const char *cpp = R"(
        class Base {
        public:
            virtual void foo() {}
        };
    )";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("Base_foo");
    EXPECT_EQ(CFunc, nullptr) << "Virtual method should be skipped";
}

// ============================================================================
// Story #19: Member Access Transformation Tests
// ============================================================================

TEST_F(CppToCVisitorTestFixture, ImplicitThisRead) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("Point_getX");
    ASSERT_NE(CFunc, nullptr) << "C function not generated";

    Stmt *Body = CFunc->getBody();
    ASSERT_NE(Body, nullptr) << "Function body not translated";
}

TEST_F(CppToCVisitorTestFixture, ImplicitThisWrite) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("Point_setX");
    ASSERT_NE(CFunc, nullptr) << "C function not generated";

    Stmt *Body = CFunc->getBody();
    ASSERT_NE(Body, nullptr) << "Function body not translated";
}

TEST_F(CppToCVisitorTestFixture, ExplicitMemberAccess) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("Point_distance");
    ASSERT_NE(CFunc, nullptr) << "C function not generated";

    Stmt *Body = CFunc->getBody();
    ASSERT_NE(Body, nullptr) << "Function body not translated";
}

TEST_F(CppToCVisitorTestFixture, MultipleFieldAccess) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCFunc("Rectangle_area");
    ASSERT_NE(CFunc, nullptr) << "C function not generated";

    Stmt *Body = CFunc->getBody();
    ASSERT_NE(Body, nullptr) << "Function body not translated";
}

// ============================================================================
// Story #17: Constructor Translation Tests
// ============================================================================

TEST_F(CppToCVisitorTestFixture, DefaultConstructor) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCtor("Point__ctor");
    ASSERT_NE(CFunc, nullptr) << "Constructor function not generated";
    EXPECT_EQ(CFunc->getNumParams(), 1u) << "Expected 1 parameter (this)";
    EXPECT_TRUE(CFunc->getReturnType()->isVoidType()) << "Constructor should return void";
}

TEST_F(CppToCVisitorTestFixture, MemberInitializers) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCtor("Point__ctor");
    ASSERT_NE(CFunc, nullptr) << "Constructor function not generated";
    EXPECT_EQ(CFunc->getNumParams(), 3u) << "Expected 3 parameters (this + 2 params)";

    Stmt *Body = CFunc->getBody();
    ASSERT_NE(Body, nullptr) << "Constructor body not translated";
}

TEST_F(CppToCVisitorTestFixture, ConstructorWithBody) {
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
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CFunc = visitor.getCtor("Rectangle__ctor");
    ASSERT_NE(CFunc, nullptr) << "Constructor function not generated";

    Stmt *Body = CFunc->getBody();
    ASSERT_NE(Body, nullptr) << "Constructor body not translated";
}
