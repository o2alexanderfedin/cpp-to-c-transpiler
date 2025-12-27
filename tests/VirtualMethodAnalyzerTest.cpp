/**
 * @file VirtualMethodAnalyzerTest.cpp
 * @brief Tests for Story #167: Virtual Method Detection and AST Analysis
 *
 * Acceptance Criteria:
 * - Virtual methods detected correctly
 * - Pure virtual methods identified
 * - Abstract classes recognized
 * - Inherited virtual methods tracked
 * - Unit tests pass (5+ test cases)
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <cassert>

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

// Test 1: Detect single virtual method

// Test fixture
class VirtualMethodAnalyzerTest : public ::testing::Test {
protected:
};

TEST_F(VirtualMethodAnalyzerTest, DetectSingleVirtualMethod) {
    const char *code = R"(
            class Base {
            public:
                virtual void foo();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        ASSERT_TRUE(Base) << "Base class not found";

        // Test: Class should be polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Base)) << "Base should be polymorphic";

        // Test: Should have exactly 1 virtual method
        auto virtualMethods = analyzer.getVirtualMethods(Base);
        ASSERT_TRUE(virtualMethods.size() == 1) << "Expected 1 virtual method, got: " + std::to_string(virtualMethods.size());

        // Test: Should not be abstract (no pure virtual)
        ASSERT_TRUE(!analyzer.isAbstractClass(Base)) << "Base should not be abstract";
}

TEST_F(VirtualMethodAnalyzerTest, DetectPureVirtualMethod) {
    const char *code = R"(
            class Abstract {
            public:
                virtual void foo() = 0;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Abstract = findClass(TU, "Abstract");
        ASSERT_TRUE(Abstract) << "Abstract class not found";

        // Test: Class should be polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Abstract)) << "Abstract should be polymorphic";

        // Test: Class should be abstract
        ASSERT_TRUE(analyzer.isAbstractClass(Abstract)) << "Abstract should be abstract class";

        // Test: Method should be pure virtual
        auto virtualMethods = analyzer.getVirtualMethods(Abstract);
        ASSERT_TRUE(virtualMethods.size() == 1) << "Expected 1 virtual method";
        ASSERT_TRUE(analyzer.isPureVirtual(virtualMethods[0])) << "foo() should be pure virtual";
}

TEST_F(VirtualMethodAnalyzerTest, DetectMultipleVirtualMethods) {
    const char *code = R"(
            class Shape {
            public:
                virtual void draw();
                virtual double area();
                virtual void setColor(int c);
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Shape = findClass(TU, "Shape");
        ASSERT_TRUE(Shape) << "Shape class not found";

        // Test: Class should be polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Shape)) << "Shape should be polymorphic";

        // Test: Should have 3 virtual methods
        auto virtualMethods = analyzer.getVirtualMethods(Shape);
        ASSERT_TRUE(virtualMethods.size() == 3) << "Expected 3 virtual methods, got: " + std::to_string(virtualMethods.size());
}

TEST_F(VirtualMethodAnalyzerTest, DetectInheritedVirtualMethods) {
    const char *code = R"(
            class Base {
            public:
                virtual void foo();
            };

            class Derived : public Base {
            public:
                void foo() override;
                virtual void bar();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        // Test: Both should be polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Base)) << "Base should be polymorphic";
        ASSERT_TRUE(analyzer.isPolymorphic(Derived)) << "Derived should be polymorphic";

        // Test: Base has 1 virtual method
        auto baseMethods = analyzer.getVirtualMethods(Base);
        ASSERT_TRUE(baseMethods.size() == 1) << "Base should have 1 virtual method";

        // Test: Derived has 2 virtual methods (foo override + bar)
        auto derivedMethods = analyzer.getVirtualMethods(Derived);
        ASSERT_TRUE(derivedMethods.size() == 2) << "Expected 2 virtual methods in Derived, got: " + std::to_string(derivedMethods.size());
}

TEST_F(VirtualMethodAnalyzerTest, NonPolymorphicClass) {
    const char *code = R"(
            class Regular {
            public:
                void foo();
                int bar();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Regular = findClass(TU, "Regular");
        ASSERT_TRUE(Regular) << "Regular class not found";

        // Test: Class should NOT be polymorphic
        ASSERT_TRUE(!analyzer.isPolymorphic(Regular)) << "Regular should not be polymorphic";

        // Test: Should have 0 virtual methods
        auto virtualMethods = analyzer.getVirtualMethods(Regular);
        ASSERT_TRUE(virtualMethods.size() == 0) << "Expected 0 virtual methods, got: " + std::to_string(virtualMethods.size());

        // Test: Should not be abstract
        ASSERT_TRUE(!analyzer.isAbstractClass(Regular)) << "Regular should not be abstract";
}

TEST_F(VirtualMethodAnalyzerTest, MixedVirtualMethods) {
    const char *code = R"(
            class Mixed {
            public:
                void normalMethod();
                virtual void virtualMethod1();
                int anotherNormal();
                virtual void virtualMethod2();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Mixed = findClass(TU, "Mixed");
        ASSERT_TRUE(Mixed) << "Mixed class not found";

        // Test: Class should be polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Mixed)) << "Mixed should be polymorphic";

        // Test: Should have exactly 2 virtual methods
        auto virtualMethods = analyzer.getVirtualMethods(Mixed);
        ASSERT_TRUE(virtualMethods.size() == 2) << "Expected 2 virtual methods, got: " + std::to_string(virtualMethods.size());
}

TEST_F(VirtualMethodAnalyzerTest, VirtualDestructor) {
    const char *code = R"(
            class WithVirtualDestructor {
            public:
                virtual ~WithVirtualDestructor();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        VirtualMethodAnalyzer analyzer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *WithVirtualDestructor = findClass(TU, "WithVirtualDestructor");
        ASSERT_TRUE(WithVirtualDestructor) << "WithVirtualDestructor class not found";

        // Test: Class should be polymorphic (virtual destructor counts)
        ASSERT_TRUE(analyzer.isPolymorphic(WithVirtualDestructor)) << "Class with virtual destructor should be polymorphic";

        // Test: Should have virtual methods (destructor is a virtual method)
        auto virtualMethods = analyzer.getVirtualMethods(WithVirtualDestructor);
        ASSERT_TRUE(virtualMethods.size() >= 1) << "Expected at least 1 virtual method (destructor)";
}
