/**
 * @file PureVirtualHandlerTest.cpp
 * @brief Tests for Story #173: Pure Virtual Function Support
 *
 * Tests detection of pure virtual methods and abstract classes.
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/PureVirtualHandler.h"
#include <vector>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Test fixture
class PureVirtualHandlerTest : public ::testing::Test {
protected:
};

TEST_F(PureVirtualHandlerTest, DetectPureVirtualMethod) {
    const char *code = R"(
            class Shape {
            public:
                virtual void draw() = 0;  // Pure virtual
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler handler(Context, analyzer);

        // Find the Shape class
        CXXRecordDecl* Shape = nullptr;
        for (auto *D : Context.getTranslationUnitDecl()->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == "Shape" && RD->isCompleteDefinition()) {
                    Shape = RD;
                    break;
                }
            }
        }

        ASSERT_TRUE(Shape) << "Shape class not found";

        // Check that draw() is pure virtual
        bool foundPureVirtual = false;
        for (auto* method : Shape->methods()) {
            if (method->getNameAsString() == "draw") {
                foundPureVirtual = handler.isPureVirtual(method);
                break;
            }
        }

        ASSERT_TRUE(foundPureVirtual) << "draw(;should be detected as pure virtual");
}

TEST_F(PureVirtualHandlerTest, DetectAbstractClass) {
    const char *code = R"(
            class AbstractShape {
            public:
                virtual void draw() = 0;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler handler(Context, analyzer);

        // Find the AbstractShape class
        CXXRecordDecl* AbstractShape = nullptr;
        for (auto *D : Context.getTranslationUnitDecl()->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == "AbstractShape" && RD->isCompleteDefinition()) {
                    AbstractShape = RD;
                    break;
                }
            }
        }

        ASSERT_TRUE(AbstractShape) << "AbstractShape class not found";
        ASSERT_TRUE(handler.isAbstractClass(AbstractShape)) << "AbstractShape should be detected as abstract";
}

TEST_F(PureVirtualHandlerTest, NonAbstractClassNotDetected) {
    const char *code = R"(
            class ConcreteShape {
            public:
                virtual void draw() {}  // Not pure virtual
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler handler(Context, analyzer);

        // Find the ConcreteShape class
        CXXRecordDecl* ConcreteShape = nullptr;
        for (auto *D : Context.getTranslationUnitDecl()->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == "ConcreteShape" && RD->isCompleteDefinition()) {
                    ConcreteShape = RD;
                    break;
                }
            }
        }

        ASSERT_TRUE(ConcreteShape) << "ConcreteShape class not found";
        ASSERT_TRUE(!handler.isAbstractClass(ConcreteShape)) << "ConcreteShape should NOT be detected as abstract";
}

TEST_F(PureVirtualHandlerTest, MultiplePureVirtualMethods) {
    const char *code = R"(
            class Interface {
            public:
                virtual void method1() = 0;
                virtual void method2() = 0;
                virtual int method3() = 0;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler handler(Context, analyzer);

        // Find the Interface class
        CXXRecordDecl* Interface = nullptr;
        for (auto *D : Context.getTranslationUnitDecl()->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == "Interface" && RD->isCompleteDefinition()) {
                    Interface = RD;
                    break;
                }
            }
        }

        ASSERT_TRUE(Interface) << "Interface class not found";

        auto pureVirtualMethods = handler.getPureVirtualMethods(Interface);
        ASSERT_TRUE(pureVirtualMethods.size() == 3) << "Should detect 3 pure virtual methods";
}

TEST_F(PureVirtualHandlerTest, MixedVirtualAndPureVirtual) {
    const char *code = R"(
            class MixedClass {
            public:
                virtual void concrete() {}    // Regular virtual
                virtual void abstract() = 0;  // Pure virtual
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler handler(Context, analyzer);

        // Find the MixedClass class
        CXXRecordDecl* MixedClass = nullptr;
        for (auto *D : Context.getTranslationUnitDecl()->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == "MixedClass" && RD->isCompleteDefinition()) {
                    MixedClass = RD;
                    break;
                }
            }
        }

        ASSERT_TRUE(MixedClass) << "MixedClass class not found";
        ASSERT_TRUE(handler.isAbstractClass(MixedClass)) << "Class with any pure virtual should be abstract";

        auto pureVirtualMethods = handler.getPureVirtualMethods(MixedClass);
        ASSERT_TRUE(pureVirtualMethods.size() == 1) << "Should detect 1 pure virtual method";
}

TEST_F(PureVirtualHandlerTest, DerivedConcreteClass) {
    const char *code = R"(
            class Abstract {
            public:
                virtual void method() = 0;
            };

            class Concrete : public Abstract {
            public:
                void method() override {}  // Provides implementation
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler handler(Context, analyzer);

        // Find both classes
        CXXRecordDecl* Abstract = nullptr;
        CXXRecordDecl* Concrete = nullptr;
        for (auto *D : Context.getTranslationUnitDecl()->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (!RD->isCompleteDefinition()) continue;
                if (RD->getNameAsString() == "Abstract") {
                    Abstract = RD;
                } else if (RD->getNameAsString() == "Concrete") {
                    Concrete = RD;
                }
            }
        }

        ASSERT_TRUE(Abstract) << "Abstract class not found";
        ASSERT_TRUE(Concrete) << "Concrete class not found";

        ASSERT_TRUE(handler.isAbstractClass(Abstract)) << "Base class should be abstract";
        ASSERT_TRUE(!handler.isAbstractClass(Concrete)) << "Derived class overriding all pure virtuals should be concrete";
}

TEST_F(PureVirtualHandlerTest, DerivedAbstractClass) {
    const char *code = R"(
            class Base {
            public:
                virtual void method1() = 0;
                virtual void method2() = 0;
            };

            class Derived : public Base {
            public:
                void method1() override {}  // Overrides method1 only
                // method2 remains pure virtual
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler handler(Context, analyzer);

        // Find both classes
        CXXRecordDecl* Base = nullptr;
        CXXRecordDecl* Derived = nullptr;
        for (auto *D : Context.getTranslationUnitDecl()->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (!RD->isCompleteDefinition()) continue;
                if (RD->getNameAsString() == "Base") {
                    Base = RD;
                } else if (RD->getNameAsString() == "Derived") {
                    Derived = RD;
                }
            }
        }

        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        ASSERT_TRUE(handler.isAbstractClass(Base)) << "Base class should be abstract";
        ASSERT_TRUE(handler.isAbstractClass(Derived)) << "Derived class not overriding all pure virtuals should remain abstract";
}
