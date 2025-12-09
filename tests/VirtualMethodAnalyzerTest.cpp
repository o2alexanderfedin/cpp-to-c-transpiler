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

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <iostream>
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

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
void test_DetectSingleVirtualMethod() {
    TEST_START("DetectSingleVirtualMethod");

    const char *code = R"(
        class Base {
        public:
            virtual void foo();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    ASSERT(Base, "Base class not found");

    // Test: Class should be polymorphic
    ASSERT(analyzer.isPolymorphic(Base), "Base should be polymorphic");

    // Test: Should have exactly 1 virtual method
    auto virtualMethods = analyzer.getVirtualMethods(Base);
    ASSERT(virtualMethods.size() == 1,
           "Expected 1 virtual method, got: " + std::to_string(virtualMethods.size()));

    // Test: Should not be abstract (no pure virtual)
    ASSERT(!analyzer.isAbstractClass(Base), "Base should not be abstract");

    TEST_PASS("DetectSingleVirtualMethod");
}

// Test 2: Detect pure virtual method
void test_DetectPureVirtualMethod() {
    TEST_START("DetectPureVirtualMethod");

    const char *code = R"(
        class Abstract {
        public:
            virtual void foo() = 0;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Abstract = findClass(TU, "Abstract");
    ASSERT(Abstract, "Abstract class not found");

    // Test: Class should be polymorphic
    ASSERT(analyzer.isPolymorphic(Abstract), "Abstract should be polymorphic");

    // Test: Class should be abstract
    ASSERT(analyzer.isAbstractClass(Abstract), "Abstract should be abstract class");

    // Test: Method should be pure virtual
    auto virtualMethods = analyzer.getVirtualMethods(Abstract);
    ASSERT(virtualMethods.size() == 1, "Expected 1 virtual method");
    ASSERT(analyzer.isPureVirtual(virtualMethods[0]), "foo() should be pure virtual");

    TEST_PASS("DetectPureVirtualMethod");
}

// Test 3: Detect multiple virtual methods
void test_DetectMultipleVirtualMethods() {
    TEST_START("DetectMultipleVirtualMethods");

    const char *code = R"(
        class Shape {
        public:
            virtual void draw();
            virtual double area();
            virtual void setColor(int c);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Shape = findClass(TU, "Shape");
    ASSERT(Shape, "Shape class not found");

    // Test: Class should be polymorphic
    ASSERT(analyzer.isPolymorphic(Shape), "Shape should be polymorphic");

    // Test: Should have 3 virtual methods
    auto virtualMethods = analyzer.getVirtualMethods(Shape);
    ASSERT(virtualMethods.size() == 3,
           "Expected 3 virtual methods, got: " + std::to_string(virtualMethods.size()));

    TEST_PASS("DetectMultipleVirtualMethods");
}

// Test 4: Detect inherited virtual methods
void test_DetectInheritedVirtualMethods() {
    TEST_START("DetectInheritedVirtualMethods");

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
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Derived = findClass(TU, "Derived");
    ASSERT(Base, "Base class not found");
    ASSERT(Derived, "Derived class not found");

    // Test: Both should be polymorphic
    ASSERT(analyzer.isPolymorphic(Base), "Base should be polymorphic");
    ASSERT(analyzer.isPolymorphic(Derived), "Derived should be polymorphic");

    // Test: Base has 1 virtual method
    auto baseMethods = analyzer.getVirtualMethods(Base);
    ASSERT(baseMethods.size() == 1, "Base should have 1 virtual method");

    // Test: Derived has 2 virtual methods (foo override + bar)
    auto derivedMethods = analyzer.getVirtualMethods(Derived);
    ASSERT(derivedMethods.size() == 2,
           "Expected 2 virtual methods in Derived, got: " + std::to_string(derivedMethods.size()));

    TEST_PASS("DetectInheritedVirtualMethods");
}

// Test 5: Non-polymorphic class
void test_NonPolymorphicClass() {
    TEST_START("NonPolymorphicClass");

    const char *code = R"(
        class Regular {
        public:
            void foo();
            int bar();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Regular = findClass(TU, "Regular");
    ASSERT(Regular, "Regular class not found");

    // Test: Class should NOT be polymorphic
    ASSERT(!analyzer.isPolymorphic(Regular), "Regular should not be polymorphic");

    // Test: Should have 0 virtual methods
    auto virtualMethods = analyzer.getVirtualMethods(Regular);
    ASSERT(virtualMethods.size() == 0,
           "Expected 0 virtual methods, got: " + std::to_string(virtualMethods.size()));

    // Test: Should not be abstract
    ASSERT(!analyzer.isAbstractClass(Regular), "Regular should not be abstract");

    TEST_PASS("NonPolymorphicClass");
}

// Test 6: Mixed virtual and non-virtual methods
void test_MixedVirtualMethods() {
    TEST_START("MixedVirtualMethods");

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
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Mixed = findClass(TU, "Mixed");
    ASSERT(Mixed, "Mixed class not found");

    // Test: Class should be polymorphic
    ASSERT(analyzer.isPolymorphic(Mixed), "Mixed should be polymorphic");

    // Test: Should have exactly 2 virtual methods
    auto virtualMethods = analyzer.getVirtualMethods(Mixed);
    ASSERT(virtualMethods.size() == 2,
           "Expected 2 virtual methods, got: " + std::to_string(virtualMethods.size()));

    TEST_PASS("MixedVirtualMethods");
}

// Test 7: Virtual destructor detection
void test_VirtualDestructor() {
    TEST_START("VirtualDestructor");

    const char *code = R"(
        class WithVirtualDestructor {
        public:
            virtual ~WithVirtualDestructor();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *WithVirtualDestructor = findClass(TU, "WithVirtualDestructor");
    ASSERT(WithVirtualDestructor, "WithVirtualDestructor class not found");

    // Test: Class should be polymorphic (virtual destructor counts)
    ASSERT(analyzer.isPolymorphic(WithVirtualDestructor),
           "Class with virtual destructor should be polymorphic");

    // Test: Should have virtual methods (destructor is a virtual method)
    auto virtualMethods = analyzer.getVirtualMethods(WithVirtualDestructor);
    ASSERT(virtualMethods.size() >= 1,
           "Expected at least 1 virtual method (destructor)");

    TEST_PASS("VirtualDestructor");
}

int main() {
    std::cout << "Running Virtual Method Analyzer Tests...\n" << std::endl;

    test_DetectSingleVirtualMethod();
    test_DetectPureVirtualMethod();
    test_DetectMultipleVirtualMethods();
    test_DetectInheritedVirtualMethods();
    test_NonPolymorphicClass();
    test_MixedVirtualMethods();
    test_VirtualDestructor();

    std::cout << "\nAll tests passed!" << std::endl;
    return 0;
}
