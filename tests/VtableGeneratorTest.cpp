/**
 * @file VtableGeneratorTest.cpp
 * @brief Tests for Story #168: Vtable Struct Generation
 *
 * Acceptance Criteria:
 * - Vtable structs generated for all polymorphic classes
 * - Function pointers have correct types
 * - Method order matches C++ ABI (destructor first)
 * - Unit tests pass (8+ test cases)
 * - Integration tests with inheritance
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VtableGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/OverrideResolver.h"
#include <cassert>
#include <sstream>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros (removed - using GTest ASSERT macros instead)

// Helper function to find class by name
CXXRecordDecl* findClass(TranslationUnitDecl* TU, const std::string& name) {
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                return RD;
            }
        }
    }
    return nullptr;
}

// Test 1: Generate simple vtable struct

// Test fixture
class VtableGeneratorTest : public ::testing::Test {
protected:
};

TEST_F(VtableGeneratorTest, GenerateSimpleVtable) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                virtual void foo() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        OverrideResolver resolver(AST->getASTContext(), analyzer);
        VtableGenerator generator(AST->getASTContext(), analyzer, &resolver);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        ASSERT_TRUE(Base) << "Base class not found";

        // Generate vtable struct
        std::string vtableCode = generator.generateVtableStruct(Base);

        // Verify vtable struct contains correct elements
        ASSERT_TRUE(vtableCode.find("struct Base_vtable") != std::string::npos) << "Expected 'struct Base_vtable' in output";
        ASSERT_TRUE(vtableCode.find("void (*destructor)") != std::string::npos ||
               vtableCode.find("void (*__dtor)") != std::string::npos) << "Expected destructor function pointer";
        ASSERT_TRUE(vtableCode.find("void (*foo)") != std::string::npos) << "Expected foo function pointer";
}

TEST_F(VtableGeneratorTest, VtableMethodOrder) {
    const char *code = R"(
            class Shape {
            public:
                virtual ~Shape() {}
                virtual double area() { return 0.0; }
                virtual void draw() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        OverrideResolver resolver(AST->getASTContext(), analyzer);
        VtableGenerator generator(AST->getASTContext(), analyzer, &resolver);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Shape = findClass(TU, "Shape");
        ASSERT_TRUE(Shape) << "Shape class not found";

        // Get method order
        auto methods = generator.getVtableMethodOrder(Shape);

        ASSERT_TRUE(methods.size() >= 2) << "Expected at least 2 methods (destructor + virtual methods)";

        // First method should be destructor
        ASSERT_TRUE(isa<CXXDestructorDecl>(methods[0]) || methods[0]->getNameAsString().find("dtor") != std::string::npos) << "First method should be destructor";
}

TEST_F(VtableGeneratorTest, MultipleVirtualMethods) {
    const char *code = R"(
            class Widget {
            public:
                virtual ~Widget() {}
                virtual void render() {}
                virtual void update() {}
                virtual bool validate() { return true; }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        OverrideResolver resolver(AST->getASTContext(), analyzer);
        VtableGenerator generator(AST->getASTContext(), analyzer, &resolver);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Widget = findClass(TU, "Widget");
        ASSERT_TRUE(Widget) << "Widget class not found";

        std::string vtableCode = generator.generateVtableStruct(Widget);

        // Verify all methods present
        ASSERT_TRUE(vtableCode.find("struct Widget_vtable") != std::string::npos) << "Expected vtable struct name";
        ASSERT_TRUE(vtableCode.find("render") != std::string::npos) << "Expected render method";
        ASSERT_TRUE(vtableCode.find("update") != std::string::npos) << "Expected update method";
        ASSERT_TRUE(vtableCode.find("validate") != std::string::npos) << "Expected validate method";
}

TEST_F(VtableGeneratorTest, InheritedVirtualMethods) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                virtual void foo() {}
            };

            class Derived : public Base {
            public:
                void foo() override {}
                virtual void bar() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        OverrideResolver resolver(AST->getASTContext(), analyzer);
        VtableGenerator generator(AST->getASTContext(), analyzer, &resolver);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        std::string vtableCode = generator.generateVtableStruct(Derived);

        // Verify derived vtable includes both inherited and new methods
        ASSERT_TRUE(vtableCode.find("struct Derived_vtable") != std::string::npos) << "Expected Derived_vtable struct";
        ASSERT_TRUE(vtableCode.find("foo") != std::string::npos) << "Expected foo (overridden method)";
        ASSERT_TRUE(vtableCode.find("bar") != std::string::npos) << "Expected bar (new method)";
}

TEST_F(VtableGeneratorTest, FunctionPointerTypes) {
    const char *code = R"(
            class Calculator {
            public:
                virtual ~Calculator() {}
                virtual int add(int a, int b) { return a + b; }
                virtual double multiply(double x, double y) { return x * y; }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        OverrideResolver resolver(AST->getASTContext(), analyzer);
        VtableGenerator generator(AST->getASTContext(), analyzer, &resolver);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Calculator = findClass(TU, "Calculator");
        ASSERT_TRUE(Calculator) << "Calculator class not found";

        std::string vtableCode = generator.generateVtableStruct(Calculator);

        // Verify function pointer signatures
        ASSERT_TRUE(vtableCode.find("int (*add)") != std::string::npos) << "Expected 'int (*add)' function pointer";
        ASSERT_TRUE(vtableCode.find("double (*multiply)") != std::string::npos ||
               vtableCode.find("float (*multiply)") != std::string::npos) << "Expected 'double (*multiply)' function pointer";
}

TEST_F(VtableGeneratorTest, NonPolymorphicClass) {
    const char *code = R"(
            class Regular {
            public:
                void foo() {}
                int bar() { return 42; }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        OverrideResolver resolver(AST->getASTContext(), analyzer);
        VtableGenerator generator(AST->getASTContext(), analyzer, &resolver);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Regular = findClass(TU, "Regular");
        ASSERT_TRUE(Regular) << "Regular class not found";

        std::string vtableCode = generator.generateVtableStruct(Regular);

        // Non-polymorphic class should not generate vtable
        ASSERT_TRUE(vtableCode.empty() || vtableCode.find("// Not polymorphic") != std::string::npos) << "Non-polymorphic class should not generate vtable";
}

TEST_F(VtableGeneratorTest, PureVirtualMethods) {
    const char *code = R"(
            class Abstract {
            public:
                virtual ~Abstract() {}
                virtual void foo() = 0;
                virtual int bar() = 0;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        OverrideResolver resolver(AST->getASTContext(), analyzer);
        VtableGenerator generator(AST->getASTContext(), analyzer, &resolver);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Abstract = findClass(TU, "Abstract");
        ASSERT_TRUE(Abstract) << "Abstract class not found";

        std::string vtableCode = generator.generateVtableStruct(Abstract);

        // Abstract class should still generate vtable struct
        ASSERT_TRUE(vtableCode.find("struct Abstract_vtable") != std::string::npos) << "Expected vtable struct for abstract class";
        ASSERT_TRUE(vtableCode.find("foo") != std::string::npos) << "Expected pure virtual foo";
        ASSERT_TRUE(vtableCode.find("bar") != std::string::npos) << "Expected pure virtual bar";
}

TEST_F(VtableGeneratorTest, ComplexInheritance) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                virtual void foo() {}
            };

            class Middle : public Base {
            public:
                void foo() override {}
                virtual void bar() {}
            };

            class Derived : public Middle {
            public:
                void bar() override {}
                virtual void baz() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        OverrideResolver resolver(AST->getASTContext(), analyzer);
        VtableGenerator generator(AST->getASTContext(), analyzer, &resolver);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        std::string vtableCode = generator.generateVtableStruct(Derived);

        // Verify all methods in hierarchy
        ASSERT_TRUE(vtableCode.find("struct Derived_vtable") != std::string::npos) << "Expected Derived_vtable";
        ASSERT_TRUE(vtableCode.find("foo") != std::string::npos) << "Expected inherited foo";
        ASSERT_TRUE(vtableCode.find("bar") != std::string::npos) << "Expected overridden bar";
        ASSERT_TRUE(vtableCode.find("baz") != std::string::npos) << "Expected new baz";
}
