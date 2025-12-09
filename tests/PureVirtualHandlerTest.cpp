/**
 * @file PureVirtualHandlerTest.cpp
 * @brief Tests for Story #173: Pure Virtual Function Support
 *
 * Tests detection of pure virtual methods and abstract classes.
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/PureVirtualHandler.h"
#include <iostream>
#include <vector>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Test 1: Detect pure virtual method
void test_DetectPureVirtualMethod() {
    TEST_START("DetectPureVirtualMethod");

    const char *code = R"(
        class Shape {
        public:
            virtual void draw() = 0;  // Pure virtual
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(Shape, "Shape class not found");

    // Check that draw() is pure virtual
    bool foundPureVirtual = false;
    for (auto* method : Shape->methods()) {
        if (method->getNameAsString() == "draw") {
            foundPureVirtual = handler.isPureVirtual(method);
            break;
        }
    }

    ASSERT(foundPureVirtual, "draw() should be detected as pure virtual");

    TEST_PASS("DetectPureVirtualMethod");
}

// Test 2: Detect abstract class
void test_DetectAbstractClass() {
    TEST_START("DetectAbstractClass");

    const char *code = R"(
        class AbstractShape {
        public:
            virtual void draw() = 0;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(AbstractShape, "AbstractShape class not found");
    ASSERT(handler.isAbstractClass(AbstractShape),
           "AbstractShape should be detected as abstract");

    TEST_PASS("DetectAbstractClass");
}

// Test 3: Non-abstract class should not be detected
void test_NonAbstractClassNotDetected() {
    TEST_START("NonAbstractClassNotDetected");

    const char *code = R"(
        class ConcreteShape {
        public:
            virtual void draw() {}  // Not pure virtual
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(ConcreteShape, "ConcreteShape class not found");
    ASSERT(!handler.isAbstractClass(ConcreteShape),
           "ConcreteShape should NOT be detected as abstract");

    TEST_PASS("NonAbstractClassNotDetected");
}

// Test 4: Multiple pure virtual methods
void test_MultiplePureVirtualMethods() {
    TEST_START("MultiplePureVirtualMethods");

    const char *code = R"(
        class Interface {
        public:
            virtual void method1() = 0;
            virtual void method2() = 0;
            virtual int method3() = 0;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(Interface, "Interface class not found");

    auto pureVirtualMethods = handler.getPureVirtualMethods(Interface);
    ASSERT(pureVirtualMethods.size() == 3,
           "Should detect 3 pure virtual methods");

    TEST_PASS("MultiplePureVirtualMethods");
}

// Test 5: Mixed virtual and pure virtual methods
void test_MixedVirtualAndPureVirtual() {
    TEST_START("MixedVirtualAndPureVirtual");

    const char *code = R"(
        class MixedClass {
        public:
            virtual void concrete() {}    // Regular virtual
            virtual void abstract() = 0;  // Pure virtual
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(MixedClass, "MixedClass class not found");
    ASSERT(handler.isAbstractClass(MixedClass),
           "Class with any pure virtual should be abstract");

    auto pureVirtualMethods = handler.getPureVirtualMethods(MixedClass);
    ASSERT(pureVirtualMethods.size() == 1,
           "Should detect 1 pure virtual method");

    TEST_PASS("MixedVirtualAndPureVirtual");
}

// Test 6: Derived class overriding pure virtual becomes concrete
void test_DerivedConcreteClass() {
    TEST_START("DerivedConcreteClass");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(Abstract, "Abstract class not found");
    ASSERT(Concrete, "Concrete class not found");

    ASSERT(handler.isAbstractClass(Abstract),
           "Base class should be abstract");
    ASSERT(!handler.isAbstractClass(Concrete),
           "Derived class overriding all pure virtuals should be concrete");

    TEST_PASS("DerivedConcreteClass");
}

// Test 7: Derived class not overriding pure virtual remains abstract
void test_DerivedAbstractClass() {
    TEST_START("DerivedAbstractClass");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(Base, "Base class not found");
    ASSERT(Derived, "Derived class not found");

    ASSERT(handler.isAbstractClass(Base),
           "Base class should be abstract");
    ASSERT(handler.isAbstractClass(Derived),
           "Derived class not overriding all pure virtuals should remain abstract");

    TEST_PASS("DerivedAbstractClass");
}

int main() {
    std::cout << "=== PureVirtualHandler Tests (Story #173) ===" << std::endl;

    test_DetectPureVirtualMethod();
    test_DetectAbstractClass();
    test_NonAbstractClassNotDetected();
    test_MultiplePureVirtualMethods();
    test_MixedVirtualAndPureVirtual();
    test_DerivedConcreteClass();
    test_DerivedAbstractClass();

    std::cout << "\n=== All PureVirtualHandler tests passed! ===" << std::endl;
    return 0;
}
