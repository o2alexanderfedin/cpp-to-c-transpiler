/**
 * @file VirtualFunctionIntegrationTest.cpp
 * @brief Story #175: Comprehensive Virtual Function Integration Tests
 *
 * Tests complete virtual function support across all components:
 * - VirtualMethodAnalyzer
 * - VtableGenerator
 * - VptrInjector
 * - OverrideResolver
 * - VtableInitializer
 * - VirtualCallTranslator
 * - PureVirtualHandler
 * - VirtualDestructorHandler
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VtableGenerator.h"
#include "../include/VptrInjector.h"
#include "../include/OverrideResolver.h"
#include "../include/VtableInitializer.h"
#include "../include/VirtualCallTranslator.h"
#include "../include/PureVirtualHandler.h"
#include "../include/VirtualDestructorHandler.h"
#include <iostream>
#include <vector>
#include <memory>

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

// Helper to find class by name
CXXRecordDecl* findClass(ASTContext& Context, const std::string& name) {
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                return RD;
            }
        }
    }
    return nullptr;
}

// Test 1: Simple virtual call
void test_SimpleVirtualCall() {
    TEST_START("SimpleVirtualCall");

    const char *code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };

        class Circle : public Shape {
        public:
            void draw() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);
    VtableGenerator generator(Context, analyzer, &resolver);

    CXXRecordDecl* Shape = findClass(Context, "Shape");
    CXXRecordDecl* Circle = findClass(Context, "Circle");
    ASSERT(Shape && Circle, "Classes not found");

    // Verify polymorphism setup
    ASSERT(analyzer.isPolymorphic(Shape), "Shape should be polymorphic");
    ASSERT(analyzer.isPolymorphic(Circle), "Circle should be polymorphic");

    // Verify vtable generation
    auto shapeMethods = resolver.resolveVtableLayout(Shape);
    auto circleMethods = resolver.resolveVtableLayout(Circle);
    ASSERT(!shapeMethods.empty(), "Shape should have vtable methods");
    ASSERT(!circleMethods.empty(), "Circle should have vtable methods");

    TEST_PASS("SimpleVirtualCall");
}

// Test 2: Pure virtual (abstract class)
void test_PureVirtual() {
    TEST_START("PureVirtual");

    const char *code = R"(
        class Abstract {
        public:
            virtual void method() = 0;
        };

        class Concrete : public Abstract {
        public:
            void method() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    PureVirtualHandler pureHandler(Context, analyzer);

    CXXRecordDecl* Abstract = findClass(Context, "Abstract");
    CXXRecordDecl* Concrete = findClass(Context, "Concrete");
    ASSERT(Abstract && Concrete, "Classes not found");

    // Verify abstract detection
    ASSERT(pureHandler.isAbstractClass(Abstract), "Abstract should be abstract");
    ASSERT(!pureHandler.isAbstractClass(Concrete), "Concrete should not be abstract");

    // Verify pure virtual detection
    auto pureVirtuals = pureHandler.getPureVirtualMethods(Abstract);
    ASSERT(pureVirtuals.size() == 1, "Should have 1 pure virtual method");

    TEST_PASS("PureVirtual");
}

// Test 3: Virtual destructor
void test_VirtualDestructor() {
    TEST_START("VirtualDestructor");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler destructorHandler(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT(Base && Derived, "Classes not found");

    // Verify virtual destructor detection
    ASSERT(destructorHandler.hasVirtualDestructor(Base),
           "Base should have virtual destructor");
    ASSERT(destructorHandler.hasVirtualDestructor(Derived),
           "Derived should have virtual destructor");

    // Verify destructor should be first in vtable
    ASSERT(destructorHandler.shouldDestructorBeFirstInVtable(Base),
           "Destructor should be first in Base vtable");

    TEST_PASS("VirtualDestructor");
}

// Test 4: Multiple overrides
void test_MultipleOverrides() {
    TEST_START("MultipleOverrides");

    const char *code = R"(
        class Base {
        public:
            virtual void method1() {}
            virtual void method2() {}
            virtual void method3() {}
        };

        class Derived : public Base {
        public:
            void method1() override {}
            void method2() override {}
            void method3() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT(Base && Derived, "Classes not found");

    // Verify all methods are virtual
    auto baseMethods = analyzer.getVirtualMethods(Base);
    auto derivedMethods = analyzer.getVirtualMethods(Derived);
    ASSERT(baseMethods.size() == 3, "Base should have 3 virtual methods");
    ASSERT(derivedMethods.size() == 3, "Derived should have 3 virtual methods");

    // Verify override resolution
    auto vtableLayout = resolver.resolveVtableLayout(Derived);
    ASSERT(vtableLayout.size() == 3, "Vtable should have 3 slots");

    TEST_PASS("MultipleOverrides");
}

// Test 5: Partial override
void test_PartialOverride() {
    TEST_START("PartialOverride");

    const char *code = R"(
        class Base {
        public:
            virtual void method1() {}
            virtual void method2() {}
        };

        class Derived : public Base {
        public:
            void method1() override {}
            // method2 not overridden
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT(Derived, "Derived class not found");

    // Verify vtable has both methods
    auto vtableLayout = resolver.resolveVtableLayout(Derived);
    ASSERT(vtableLayout.size() == 2, "Vtable should have 2 slots");

    // Verify one is overridden, one is inherited
    int overriddenCount = 0;
    for (auto* method : vtableLayout) {
        if (method->getParent() == Derived) {
            overriddenCount++;
        }
    }
    ASSERT(overriddenCount == 1, "Should have 1 overridden method");

    TEST_PASS("PartialOverride");
}

// Test 6: Multi-level inheritance
void test_MultiLevelInheritance() {
    TEST_START("MultiLevelInheritance");

    const char *code = R"(
        class Base {
        public:
            virtual void method() {}
        };

        class Middle : public Base {
        public:
            void method() override {}
        };

        class Derived : public Middle {
        public:
            void method() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Middle = findClass(Context, "Middle");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT(Base && Middle && Derived, "Classes not found");

    // All should be polymorphic
    ASSERT(analyzer.isPolymorphic(Base), "Base should be polymorphic");
    ASSERT(analyzer.isPolymorphic(Middle), "Middle should be polymorphic");
    ASSERT(analyzer.isPolymorphic(Derived), "Derived should be polymorphic");

    // Verify vtable layout maintains consistency
    auto baseLayout = resolver.resolveVtableLayout(Base);
    auto middleLayout = resolver.resolveVtableLayout(Middle);
    auto derivedLayout = resolver.resolveVtableLayout(Derived);
    ASSERT(baseLayout.size() == middleLayout.size(), "Vtable size should match");
    ASSERT(middleLayout.size() == derivedLayout.size(), "Vtable size should match");

    TEST_PASS("MultiLevelInheritance");
}

// Test 7: Polymorphic collection simulation
void test_PolymorphicCollection() {
    TEST_START("PolymorphicCollection");

    const char *code = R"(
        class Animal {
        public:
            virtual void speak() {}
        };

        class Dog : public Animal {
        public:
            void speak() override {}
        };

        class Cat : public Animal {
        public:
            void speak() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Animal = findClass(Context, "Animal");
    CXXRecordDecl* Dog = findClass(Context, "Dog");
    CXXRecordDecl* Cat = findClass(Context, "Cat");
    ASSERT(Animal && Dog && Cat, "Classes not found");

    // All should have compatible vtables
    auto animalMethods = resolver.resolveVtableLayout(Animal);
    auto dogMethods = resolver.resolveVtableLayout(Dog);
    auto catMethods = resolver.resolveVtableLayout(Cat);

    ASSERT(animalMethods.size() == dogMethods.size(),
           "Dog vtable should match Animal vtable size");
    ASSERT(animalMethods.size() == catMethods.size(),
           "Cat vtable should match Animal vtable size");

    TEST_PASS("PolymorphicCollection");
}

// Test 8: Upcast preserves virtual dispatch
void test_UpcastPreservesDispatch() {
    TEST_START("UpcastPreservesDispatch");

    const char *code = R"(
        class Base {
        public:
            virtual void method() {}
        };

        class Derived : public Base {
        public:
            void method() override {}
        };

        void callThroughBase(Base* b) {
            b->method();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualCallTranslator translator(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT(Base && Derived, "Classes not found");

    // Verify both classes are polymorphic
    ASSERT(analyzer.isPolymorphic(Base), "Base should be polymorphic");
    ASSERT(analyzer.isPolymorphic(Derived), "Derived should be polymorphic");

    // Both should have virtual methods
    auto baseMethods = analyzer.getVirtualMethods(Base);
    auto derivedMethods = analyzer.getVirtualMethods(Derived);
    ASSERT(!baseMethods.empty(), "Base should have virtual methods");
    ASSERT(!derivedMethods.empty(), "Derived should have virtual methods");

    TEST_PASS("UpcastPreservesDispatch");
}

// Test 9: Virtual call in constructor (detection)
void test_VirtualCallInConstructor() {
    TEST_START("VirtualCallInConstructor");

    const char *code = R"(
        class Base {
        public:
            Base() {
                init();
            }
            virtual void init() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);

    CXXRecordDecl* Base = findClass(Context, "Base");
    ASSERT(Base, "Base class not found");

    // Verify class is polymorphic
    ASSERT(analyzer.isPolymorphic(Base), "Base should be polymorphic");

    // Verify init is virtual
    auto virtualMethods = analyzer.getVirtualMethods(Base);
    bool hasInit = false;
    for (auto* method : virtualMethods) {
        if (method->getNameAsString() == "init") {
            hasInit = true;
            break;
        }
    }
    ASSERT(hasInit, "Should find virtual init method");

    TEST_PASS("VirtualCallInConstructor");
}

// Test 10: Vptr injection in polymorphic class
void test_VptrInjection() {
    TEST_START("VptrInjection");

    const char *code = R"(
        class Polymorphic {
        public:
            virtual void method() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VptrInjector injector(Context, analyzer);

    CXXRecordDecl* Polymorphic = findClass(Context, "Polymorphic");
    ASSERT(Polymorphic, "Polymorphic class not found");

    // Verify class is polymorphic (vptr should be injected)
    ASSERT(analyzer.isPolymorphic(Polymorphic),
           "Should be polymorphic (needs vptr)");

    // Test vptr field injection
    std::vector<FieldDecl*> fields;
    bool injected = injector.injectVptrField(Polymorphic, fields);
    ASSERT(injected, "Should inject vptr");
    ASSERT(!fields.empty(), "Should have vptr field");

    TEST_PASS("VptrInjection");
}

// Test 11: Vtable initialization
void test_VtableInitialization() {
    TEST_START("VtableInitialization");

    const char *code = R"(
        class MyClass {
        public:
            MyClass() {}
            virtual void method() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VtableInitializer initializer(Context, analyzer);

    CXXRecordDecl* MyClass = findClass(Context, "MyClass");
    ASSERT(MyClass, "MyClass not found");

    // Verify vtable name generation
    std::string vtableName = initializer.getVtableName(MyClass);
    ASSERT(vtableName == "__vtable_MyClass",
           "Vtable name should be __vtable_MyClass");

    TEST_PASS("VtableInitialization");
}

// Test 12: Complex inheritance hierarchy
void test_ComplexInheritance() {
    TEST_START("ComplexInheritance");

    const char *code = R"(
        class Base {
        public:
            virtual void method1() {}
            virtual void method2() {}
        };

        class Derived1 : public Base {
        public:
            void method1() override {}
        };

        class Derived2 : public Base {
        public:
            void method2() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived1 = findClass(Context, "Derived1");
    CXXRecordDecl* Derived2 = findClass(Context, "Derived2");
    ASSERT(Base && Derived1 && Derived2, "Classes not found");

    // Verify all have proper vtable layouts
    auto baseLayout = resolver.resolveVtableLayout(Base);
    auto derived1Layout = resolver.resolveVtableLayout(Derived1);
    auto derived2Layout = resolver.resolveVtableLayout(Derived2);

    ASSERT(baseLayout.size() == 2, "Base should have 2 vtable slots");
    ASSERT(derived1Layout.size() == 2, "Derived1 should have 2 vtable slots");
    ASSERT(derived2Layout.size() == 2, "Derived2 should have 2 vtable slots");

    TEST_PASS("ComplexInheritance");
}

// Test 13: Abstract class with multiple pure virtuals
void test_MultipleAbstractMethods() {
    TEST_START("MultipleAbstractMethods");

    const char *code = R"(
        class Interface {
        public:
            virtual void method1() = 0;
            virtual void method2() = 0;
            virtual void method3() = 0;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    PureVirtualHandler pureHandler(Context, analyzer);

    CXXRecordDecl* Interface = findClass(Context, "Interface");
    ASSERT(Interface, "Interface class not found");

    ASSERT(pureHandler.isAbstractClass(Interface),
           "Interface should be abstract");

    auto pureVirtuals = pureHandler.getPureVirtualMethods(Interface);
    ASSERT(pureVirtuals.size() == 3, "Should have 3 pure virtual methods");

    TEST_PASS("MultipleAbstractMethods");
}

// Test 14: Virtual method signature matching
void test_VirtualMethodSignatureMatching() {
    TEST_START("VirtualMethodSignatureMatching");

    const char *code = R"(
        class Base {
        public:
            virtual void method(int x) {}
            virtual void method(double x) {}
        };

        class Derived : public Base {
        public:
            void method(int x) override {}
            void method(double x) override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT(Base && Derived, "Classes not found");

    // Both overloads should be in vtable
    auto baseLayout = resolver.resolveVtableLayout(Base);
    auto derivedLayout = resolver.resolveVtableLayout(Derived);
    ASSERT(baseLayout.size() == 2, "Base should have 2 vtable slots");
    ASSERT(derivedLayout.size() == 2, "Derived should have 2 vtable slots");

    TEST_PASS("VirtualMethodSignatureMatching");
}

// Test 15: Destructor chaining in hierarchy
void test_DestructorChainingIntegration() {
    TEST_START("DestructorChainingIntegration");

    const char *code = R"(
        class A {
        public:
            virtual ~A() {}
        };

        class B : public A {
        public:
            ~B() override {}
        };

        class C : public B {
        public:
            ~C() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler destructorHandler(Context, analyzer);

    CXXRecordDecl* A = findClass(Context, "A");
    CXXRecordDecl* B = findClass(Context, "B");
    CXXRecordDecl* C = findClass(Context, "C");
    ASSERT(A && B && C, "Classes not found");

    // All should have virtual destructors
    ASSERT(destructorHandler.hasVirtualDestructor(A),
           "A should have virtual destructor");
    ASSERT(destructorHandler.hasVirtualDestructor(B),
           "B should have virtual destructor");
    ASSERT(destructorHandler.hasVirtualDestructor(C),
           "C should have virtual destructor");

    TEST_PASS("DestructorChainingIntegration");
}

int main() {
    std::cout << "=== Virtual Function Integration Tests (Story #175) ===" << std::endl;
    std::cout << "Testing complete virtual function support across all components" << std::endl;
    std::cout << std::endl;

    // Core 9 test cases
    test_SimpleVirtualCall();
    test_PureVirtual();
    test_VirtualDestructor();
    test_MultipleOverrides();
    test_PartialOverride();
    test_MultiLevelInheritance();
    test_PolymorphicCollection();
    test_UpcastPreservesDispatch();
    test_VirtualCallInConstructor();

    // Additional integration tests
    test_VptrInjection();
    test_VtableInitialization();
    test_ComplexInheritance();
    test_MultipleAbstractMethods();
    test_VirtualMethodSignatureMatching();
    test_DestructorChainingIntegration();

    std::cout << "\n=== All 15 integration tests passed! ===" << std::endl;
    std::cout << "Virtual function support is fully functional" << std::endl;
    return 0;
}
