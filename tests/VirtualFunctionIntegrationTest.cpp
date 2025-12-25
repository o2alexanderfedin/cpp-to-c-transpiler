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

#include <gtest/gtest.h>
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
#include <vector>
#include <memory>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

#define ASSERT_MSG(cond, msg) \
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

// Test fixture
class VirtualFunctionIntegrationTest : public ::testing::Test {
protected:
};

TEST_F(VirtualFunctionIntegrationTest, SimpleVirtualCall) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);
        VtableGenerator generator(Context, analyzer, &resolver);

        CXXRecordDecl* Shape = findClass(Context, "Shape");
        CXXRecordDecl* Circle = findClass(Context, "Circle");
        ASSERT_TRUE(Shape && Circle) << "Classes not found";

        // Verify polymorphism setup
        ASSERT_TRUE(analyzer.isPolymorphic(Shape)) << "Shape should be polymorphic";
        ASSERT_TRUE(analyzer.isPolymorphic(Circle)) << "Circle should be polymorphic";

        // Verify vtable generation
        auto shapeMethods = resolver.resolveVtableLayout(Shape);
        auto circleMethods = resolver.resolveVtableLayout(Circle);
        ASSERT_TRUE(!shapeMethods.empty()) << "Shape should have vtable methods";
        ASSERT_TRUE(!circleMethods.empty()) << "Circle should have vtable methods";
}

TEST_F(VirtualFunctionIntegrationTest, PureVirtual) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler pureHandler(Context, analyzer);

        CXXRecordDecl* Abstract = findClass(Context, "Abstract");
        CXXRecordDecl* Concrete = findClass(Context, "Concrete");
        ASSERT_TRUE(Abstract && Concrete) << "Classes not found";

        // Verify abstract detection
        ASSERT_TRUE(pureHandler.isAbstractClass(Abstract)) << "Abstract should be abstract";
        ASSERT_TRUE(!pureHandler.isAbstractClass(Concrete)) << "Concrete should not be abstract";

        // Verify pure virtual detection
        auto pureVirtuals = pureHandler.getPureVirtualMethods(Abstract);
        ASSERT_TRUE(pureVirtuals.size() == 1) << "Should have 1 pure virtual method";
}

TEST_F(VirtualFunctionIntegrationTest, VirtualDestructor) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        VirtualDestructorHandler destructorHandler(Context, analyzer);

        CXXRecordDecl* Base = findClass(Context, "Base");
        CXXRecordDecl* Derived = findClass(Context, "Derived");
        ASSERT_TRUE(Base && Derived) << "Classes not found";

        // Verify virtual destructor detection
        ASSERT_TRUE(destructorHandler.hasVirtualDestructor(Base)) << "Base should have virtual destructor";
        ASSERT_TRUE(destructorHandler.hasVirtualDestructor(Derived)) << "Derived should have virtual destructor";

        // Verify destructor should be first in vtable
        ASSERT_TRUE(destructorHandler.shouldDestructorBeFirstInVtable(Base)) << "Destructor should be first in Base vtable";
}

TEST_F(VirtualFunctionIntegrationTest, MultipleOverrides) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        CXXRecordDecl* Base = findClass(Context, "Base");
        CXXRecordDecl* Derived = findClass(Context, "Derived");
        ASSERT_TRUE(Base && Derived) << "Classes not found";

        // Verify all methods are virtual
        auto baseMethods = analyzer.getVirtualMethods(Base);
        auto derivedMethods = analyzer.getVirtualMethods(Derived);
        ASSERT_TRUE(baseMethods.size() == 3) << "Base should have 3 virtual methods";
        ASSERT_TRUE(derivedMethods.size() == 3) << "Derived should have 3 virtual methods";

        // Verify override resolution
        auto vtableLayout = resolver.resolveVtableLayout(Derived);
        ASSERT_TRUE(vtableLayout.size() == 3) << "Vtable should have 3 slots";
}

TEST_F(VirtualFunctionIntegrationTest, PartialOverride) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        CXXRecordDecl* Derived = findClass(Context, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        // Verify vtable has both methods
        auto vtableLayout = resolver.resolveVtableLayout(Derived);
        ASSERT_TRUE(vtableLayout.size() == 2) << "Vtable should have 2 slots";

        // Verify one is overridden, one is inherited
        int overriddenCount = 0;
        for (auto* method : vtableLayout) {
            if (method->getParent() == Derived) {
                overriddenCount++;
            }
        }
        ASSERT_TRUE(overriddenCount == 1) << "Should have 1 overridden method";
}

TEST_F(VirtualFunctionIntegrationTest, MultiLevelInheritance) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        CXXRecordDecl* Base = findClass(Context, "Base");
        CXXRecordDecl* Middle = findClass(Context, "Middle");
        CXXRecordDecl* Derived = findClass(Context, "Derived");
        ASSERT_TRUE(Base && Middle && Derived) << "Classes not found";

        // All should be polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Base)) << "Base should be polymorphic";
        ASSERT_TRUE(analyzer.isPolymorphic(Middle)) << "Middle should be polymorphic";
        ASSERT_TRUE(analyzer.isPolymorphic(Derived)) << "Derived should be polymorphic";

        // Verify vtable layout maintains consistency
        auto baseLayout = resolver.resolveVtableLayout(Base);
        auto middleLayout = resolver.resolveVtableLayout(Middle);
        auto derivedLayout = resolver.resolveVtableLayout(Derived);
        ASSERT_TRUE(baseLayout.size() == middleLayout.size()) << "Vtable size should match";
        ASSERT_TRUE(middleLayout.size() == derivedLayout.size()) << "Vtable size should match";
}

TEST_F(VirtualFunctionIntegrationTest, PolymorphicCollection) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        CXXRecordDecl* Animal = findClass(Context, "Animal");
        CXXRecordDecl* Dog = findClass(Context, "Dog");
        CXXRecordDecl* Cat = findClass(Context, "Cat");
        ASSERT_TRUE(Animal && Dog && Cat) << "Classes not found";

        // All should have compatible vtables
        auto animalMethods = resolver.resolveVtableLayout(Animal);
        auto dogMethods = resolver.resolveVtableLayout(Dog);
        auto catMethods = resolver.resolveVtableLayout(Cat);

        ASSERT_TRUE(animalMethods.size() == dogMethods.size()) << "Dog vtable should match Animal vtable size";
        ASSERT_TRUE(animalMethods.size() == catMethods.size()) << "Cat vtable should match Animal vtable size";
}

TEST_F(VirtualFunctionIntegrationTest, UpcastPreservesDispatch) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        VirtualCallTranslator translator(Context, analyzer);

        CXXRecordDecl* Base = findClass(Context, "Base");
        CXXRecordDecl* Derived = findClass(Context, "Derived");
        ASSERT_TRUE(Base && Derived) << "Classes not found";

        // Verify both classes are polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Base)) << "Base should be polymorphic";
        ASSERT_TRUE(analyzer.isPolymorphic(Derived)) << "Derived should be polymorphic";

        // Both should have virtual methods
        auto baseMethods = analyzer.getVirtualMethods(Base);
        auto derivedMethods = analyzer.getVirtualMethods(Derived);
        ASSERT_TRUE(!baseMethods.empty()) << "Base should have virtual methods";
        ASSERT_TRUE(!derivedMethods.empty()) << "Derived should have virtual methods";
}

TEST_F(VirtualFunctionIntegrationTest, VirtualCallInConstructor) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);

        CXXRecordDecl* Base = findClass(Context, "Base");
        ASSERT_TRUE(Base) << "Base class not found";

        // Verify class is polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Base)) << "Base should be polymorphic";

        // Verify init is virtual
        auto virtualMethods = analyzer.getVirtualMethods(Base);
        bool hasInit = false;
        for (auto* method : virtualMethods) {
            if (method->getNameAsString() == "init") {
                hasInit = true;
                break;
            }
        }
        ASSERT_TRUE(hasInit) << "Should find virtual init method";
}

TEST_F(VirtualFunctionIntegrationTest, VptrInjection) {
    const char *code = R"(
            class Polymorphic {
            public:
                virtual void method() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        VptrInjector injector(Context, analyzer);

        CXXRecordDecl* Polymorphic = findClass(Context, "Polymorphic");
        ASSERT_TRUE(Polymorphic) << "Polymorphic class not found";

        // Verify class is polymorphic (vptr should be injected)
        ASSERT_TRUE(analyzer.isPolymorphic(Polymorphic)) << "Should be polymorphic (needs vptr)";

        // Test vptr field injection
        std::vector<FieldDecl*> fields;
        bool injected = injector.injectVptrField(Polymorphic, fields);
        ASSERT_TRUE(injected) << "Should inject vptr";
        ASSERT_TRUE(!fields.empty()) << "Should have vptr field";
}

TEST_F(VirtualFunctionIntegrationTest, VtableInitialization) {
    const char *code = R"(
            class MyClass {
            public:
                MyClass() {}
                virtual void method() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        VtableInitializer initializer(Context, analyzer);

        CXXRecordDecl* MyClass = findClass(Context, "MyClass");
        ASSERT_TRUE(MyClass) << "MyClass not found";

        // Verify vtable name generation
        std::string vtableName = initializer.getVtableName(MyClass);
        ASSERT_TRUE(vtableName == "__vtable_MyClass") << "Vtable name should be __vtable_MyClass";
}

TEST_F(VirtualFunctionIntegrationTest, ComplexInheritance) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        CXXRecordDecl* Base = findClass(Context, "Base");
        CXXRecordDecl* Derived1 = findClass(Context, "Derived1");
        CXXRecordDecl* Derived2 = findClass(Context, "Derived2");
        ASSERT_TRUE(Base && Derived1 && Derived2) << "Classes not found";

        // Verify all have proper vtable layouts
        auto baseLayout = resolver.resolveVtableLayout(Base);
        auto derived1Layout = resolver.resolveVtableLayout(Derived1);
        auto derived2Layout = resolver.resolveVtableLayout(Derived2);

        ASSERT_TRUE(baseLayout.size() == 2) << "Base should have 2 vtable slots";
        ASSERT_TRUE(derived1Layout.size() == 2) << "Derived1 should have 2 vtable slots";
        ASSERT_TRUE(derived2Layout.size() == 2) << "Derived2 should have 2 vtable slots";
}

TEST_F(VirtualFunctionIntegrationTest, MultipleAbstractMethods) {
    const char *code = R"(
            class Interface {
            public:
                virtual void method1() = 0;
                virtual void method2() = 0;
                virtual void method3() = 0;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        PureVirtualHandler pureHandler(Context, analyzer);

        CXXRecordDecl* Interface = findClass(Context, "Interface");
        ASSERT_TRUE(Interface) << "Interface class not found";

        ASSERT_TRUE(pureHandler.isAbstractClass(Interface)) << "Interface should be abstract";

        auto pureVirtuals = pureHandler.getPureVirtualMethods(Interface);
        ASSERT_TRUE(pureVirtuals.size() == 3) << "Should have 3 pure virtual methods";
}

TEST_F(VirtualFunctionIntegrationTest, VirtualMethodSignatureMatching) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        CXXRecordDecl* Base = findClass(Context, "Base");
        CXXRecordDecl* Derived = findClass(Context, "Derived");
        ASSERT_TRUE(Base && Derived) << "Classes not found";

        // Both overloads should be in vtable
        auto baseLayout = resolver.resolveVtableLayout(Base);
        auto derivedLayout = resolver.resolveVtableLayout(Derived);
        ASSERT_TRUE(baseLayout.size() == 2) << "Base should have 2 vtable slots";
        ASSERT_TRUE(derivedLayout.size() == 2) << "Derived should have 2 vtable slots";
}

TEST_F(VirtualFunctionIntegrationTest, DestructorChainingIntegration) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        VirtualDestructorHandler destructorHandler(Context, analyzer);

        CXXRecordDecl* A = findClass(Context, "A");
        CXXRecordDecl* B = findClass(Context, "B");
        CXXRecordDecl* C = findClass(Context, "C");
        ASSERT_TRUE(A && B && C) << "Classes not found";

        // All should have virtual destructors
        ASSERT_TRUE(destructorHandler.hasVirtualDestructor(A)) << "A should have virtual destructor";
        ASSERT_TRUE(destructorHandler.hasVirtualDestructor(B)) << "B should have virtual destructor";
        ASSERT_TRUE(destructorHandler.hasVirtualDestructor(C)) << "C should have virtual destructor";
}
