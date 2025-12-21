// TDD Tests for HeaderSeparator - Epic #19 Implementation
// Story #137: Header/Implementation Separation

#include <gtest/gtest.h>
#include "HeaderSeparator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/Decl.h"

using namespace clang;

TEST(HeaderSeparator, CompleteStructGoesToHeader) {
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
        ASSERT_TRUE(separator.getHeaderDecls().size() == 1) << "Expected 1 header declaration";
        ASSERT_TRUE(separator.getImplDecls().size() == 0) << "Expected 0 implementation declarations";

        auto *FirstDecl = separator.getHeaderDecls()[0];
        ASSERT_TRUE(llvm::isa<clang::RecordDecl>(FirstDecl)) << "Expected RecordDecl type";
        ASSERT_TRUE(llvm::cast<clang::RecordDecl>(FirstDecl)->getName() == "Point") << "Expected struct name to be 'Point'";
}

TEST(HeaderSeparator, FunctionDeclarationGoesToHeader) {
    const char *Code = R"(
            void myFunction(int x);
        )";

        auto AST = clang::tooling::buildASTFromCode(Code);
        auto *TU = AST->getASTContext().getTranslationUnitDecl();

        HeaderSeparator separator;
        separator.analyzeTranslationUnit(TU);

        ASSERT_TRUE(separator.getHeaderDecls().size() == 1) << "Expected 1 header declaration";
        ASSERT_TRUE(separator.getImplDecls().size() == 0) << "Expected 0 implementation declarations";

        auto *FirstDecl = separator.getHeaderDecls()[0];
        ASSERT_TRUE(llvm::isa<clang::FunctionDecl>(FirstDecl)) << "Expected FunctionDecl type";
        ASSERT_TRUE(llvm::cast<clang::FunctionDecl>(FirstDecl)->getName() == "myFunction") << "Expected function name to be 'myFunction'";
}

TEST(HeaderSeparator, FunctionDefinitionGoesToBoth) {
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
        ASSERT_TRUE(separator.getImplDecls().size() == 1) << "Expected 1 implementation declaration";

        // Declaration also goes to header (same FunctionDecl, will be printed differently)
        ASSERT_TRUE(separator.getHeaderDecls().size() == 1) << "Expected 1 header declaration";

        // Both should reference the same function
        auto *ImplDecl = llvm::cast<clang::FunctionDecl>(separator.getImplDecls()[0]);
        auto *HeaderDecl = llvm::cast<clang::FunctionDecl>(separator.getHeaderDecls()[0]);

        ASSERT_TRUE(ImplDecl->hasBody()) << "Implementation declaration should have body";
        ASSERT_TRUE(ImplDecl->getName() == "myFunction") << "Expected function name to be 'myFunction'";
}

TEST(HeaderSeparator, ClassWithMethods) {
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

        ASSERT_TRUE(separator.getHeaderDecls().size() == 5) << "Expected 5 header declarations (1 class + 4 method declarations;");

        ASSERT_TRUE(separator.getImplDecls().size() == 4) << "Expected 4 implementation declarations (4 methods with bodies;");
}

TEST(HeaderSeparator, EmptyTranslationUnit) {
    const char *Code = "";

        auto AST = clang::tooling::buildASTFromCode(Code);
        auto *TU = AST->getASTContext().getTranslationUnitDecl();

        HeaderSeparator separator;
        separator.analyzeTranslationUnit(TU);

        // Empty TU → empty lists
        ASSERT_TRUE(separator.getHeaderDecls().size() == 0) << "Expected 0 header declarations";
        ASSERT_TRUE(separator.getImplDecls().size() == 0) << "Expected 0 implementation declarations";
}

TEST(HeaderSeparator, MultipleClasses) {
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
        ASSERT_TRUE(separator.getHeaderDecls().size() == 3) << "Expected 3 header declarations (Point, Circle, Rectangle;");
        ASSERT_TRUE(separator.getImplDecls().size() == 0) << "Expected 0 implementation declarations";
}
