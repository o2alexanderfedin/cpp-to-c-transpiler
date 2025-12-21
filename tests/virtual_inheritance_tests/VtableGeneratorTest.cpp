/**
 * @file VtableGeneratorTest.cpp
 * @brief Tests for Story #168: Vtable Struct Generation (Migrated to GTest)
 *
 * Acceptance Criteria:
 * - Vtable structs generated for all polymorphic classes
 * - Function pointers have correct types
 * - Method order matches C++ ABI (destructor first)
 * - Unit tests pass (8 test cases)
 * - Integration tests with inheritance
 */

#include <gtest/gtest.h>
#include "../VirtualTableTestBase.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VtableGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <sstream>

using namespace clang;

// Test fixture for VtableGenerator tests
class VtableGeneratorTest : public VirtualTableTestBase {
};

// Test 1: Generate simple vtable struct
TEST_F(VtableGeneratorTest, GenerateSimpleVtable) {
    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
            virtual void foo() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    ASSERT_NE(Base, nullptr) << "Base class not found";

    // Generate vtable struct
    std::string vtableCode = generator.generateVtableStruct(Base);

    // Verify vtable struct contains correct elements
    EXPECT_NE(vtableCode.find("struct Base_vtable"), std::string::npos)
        << "Expected 'struct Base_vtable' in output";
    EXPECT_TRUE(
        vtableCode.find("void (*destructor)") != std::string::npos ||
        vtableCode.find("void (*__dtor)") != std::string::npos)
        << "Expected destructor function pointer";
    EXPECT_NE(vtableCode.find("void (*foo)"), std::string::npos)
        << "Expected foo function pointer";
}

// Test 2: Vtable method order (destructor first)
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
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Shape = findClass(TU, "Shape");
    ASSERT_NE(Shape, nullptr) << "Shape class not found";

    // Get method order
    auto methods = generator.getVtableMethodOrder(Shape);

    ASSERT_GE(methods.size(), 2) << "Expected at least 2 methods (destructor + virtual methods)";

    // First method should be destructor
    EXPECT_TRUE(
        isa<CXXDestructorDecl>(methods[0]) ||
        methods[0]->getNameAsString().find("dtor") != std::string::npos)
        << "First method should be destructor";
}

// Test 3: Multiple virtual methods
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
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Widget = findClass(TU, "Widget");
    ASSERT_NE(Widget, nullptr) << "Widget class not found";

    std::string vtableCode = generator.generateVtableStruct(Widget);

    // Verify all methods present
    EXPECT_NE(vtableCode.find("struct Widget_vtable"), std::string::npos)
        << "Expected vtable struct name";
    EXPECT_NE(vtableCode.find("render"), std::string::npos)
        << "Expected render method";
    EXPECT_NE(vtableCode.find("update"), std::string::npos)
        << "Expected update method";
    EXPECT_NE(vtableCode.find("validate"), std::string::npos)
        << "Expected validate method";
}

// Test 4: Inherited virtual methods
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
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");
    ASSERT_NE(Derived, nullptr) << "Derived class not found";

    std::string vtableCode = generator.generateVtableStruct(Derived);

    // Verify derived vtable includes both inherited and new methods
    EXPECT_NE(vtableCode.find("struct Derived_vtable"), std::string::npos)
        << "Expected Derived_vtable struct";
    EXPECT_NE(vtableCode.find("foo"), std::string::npos)
        << "Expected foo (overridden) method";
    EXPECT_NE(vtableCode.find("bar"), std::string::npos)
        << "Expected bar (new) method";
}

// Test 5: Function pointer types
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
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Calculator = findClass(TU, "Calculator");
    ASSERT_NE(Calculator, nullptr) << "Calculator class not found";

    std::string vtableCode = generator.generateVtableStruct(Calculator);

    // Verify function pointer signatures
    EXPECT_NE(vtableCode.find("int (*add)"), std::string::npos)
        << "Expected 'int (*add)' function pointer";
    EXPECT_TRUE(
        vtableCode.find("double (*multiply)") != std::string::npos ||
        vtableCode.find("float (*multiply)") != std::string::npos)
        << "Expected 'double (*multiply)' function pointer";
}

// Test 6: Non-polymorphic class (should not generate vtable)
TEST_F(VtableGeneratorTest, NonPolymorphicClass) {
    const char *code = R"(
        class Regular {
        public:
            void foo() {}
            int bar() { return 42; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Regular = findClass(TU, "Regular");
    ASSERT_NE(Regular, nullptr) << "Regular class not found";

    std::string vtableCode = generator.generateVtableStruct(Regular);

    // Non-polymorphic class should not generate vtable
    EXPECT_TRUE(
        vtableCode.empty() ||
        vtableCode.find("// Not polymorphic") != std::string::npos)
        << "Non-polymorphic class should not generate vtable";
}

// Test 7: Pure virtual methods
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
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Abstract = findClass(TU, "Abstract");
    ASSERT_NE(Abstract, nullptr) << "Abstract class not found";

    std::string vtableCode = generator.generateVtableStruct(Abstract);

    // Abstract class should still generate vtable struct
    EXPECT_NE(vtableCode.find("struct Abstract_vtable"), std::string::npos)
        << "Expected vtable struct for abstract class";
    EXPECT_NE(vtableCode.find("foo"), std::string::npos)
        << "Expected pure virtual foo";
    EXPECT_NE(vtableCode.find("bar"), std::string::npos)
        << "Expected pure virtual bar";
}

// Test 8: Complex inheritance hierarchy
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
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");
    ASSERT_NE(Derived, nullptr) << "Derived class not found";

    std::string vtableCode = generator.generateVtableStruct(Derived);

    // Verify all methods in hierarchy
    EXPECT_NE(vtableCode.find("struct Derived_vtable"), std::string::npos)
        << "Expected Derived_vtable";
    EXPECT_NE(vtableCode.find("foo"), std::string::npos)
        << "Expected inherited foo";
    EXPECT_NE(vtableCode.find("bar"), std::string::npos)
        << "Expected overridden bar";
    EXPECT_NE(vtableCode.find("baz"), std::string::npos)
        << "Expected new baz";
}
