// tests/gtest/VirtualFunctionIntegrationTest_GTest.cpp
// Migrated from VirtualFunctionIntegrationTest.cpp
// Story #175: Comprehensive Virtual Function Integration Tests
//
// Tests complete virtual function support across all components:
// - VirtualMethodAnalyzer, VtableGenerator, VptrInjector
// - OverrideResolver, VtableInitializer, VirtualCallTranslator
// - PureVirtualHandler, VirtualDestructorHandler

#include <gtest/gtest.h>
#include "VirtualFunctionTestFixtures.h"

using namespace std;

// Test fixture for Virtual Function Integration tests
class VirtualFunctionIntegrationTest : public VirtualFunctionTestBase {
protected:
    void SetUp() override {
        // Base setup handles AST initialization
    }
};

// Test 1: Simple virtual call
TEST_F(VirtualFunctionIntegrationTest, SimpleVirtualCall) {
    const char* code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };

        class Circle : public Shape {
        public:
            void draw() override {}
        };
    )";

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);
    VtableGenerator generator(Context, analyzer, &resolver);

    CXXRecordDecl* Shape = findClass(Context, "Shape");
    CXXRecordDecl* Circle = findClass(Context, "Circle");
    ASSERT_NE(Shape, nullptr) << "Shape class not found";
    ASSERT_NE(Circle, nullptr) << "Circle class not found";

    // Verify polymorphism setup
    EXPECT_TRUE(analyzer.isPolymorphic(Shape)) << "Shape should be polymorphic";
    EXPECT_TRUE(analyzer.isPolymorphic(Circle)) << "Circle should be polymorphic";

    // Verify vtable generation
    auto shapeMethods = resolver.resolveVtableLayout(Shape);
    auto circleMethods = resolver.resolveVtableLayout(Circle);
    EXPECT_FALSE(shapeMethods.empty()) << "Shape should have vtable methods";
    EXPECT_FALSE(circleMethods.empty()) << "Circle should have vtable methods";
}

// Test 2: Pure virtual (abstract class)
TEST_F(VirtualFunctionIntegrationTest, PureVirtual) {
    const char* code = R"(
        class Abstract {
        public:
            virtual void method() = 0;
        };

        class Concrete : public Abstract {
        public:
            void method() override {}
        };
    )";

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    PureVirtualHandler pureHandler(Context, analyzer);

    CXXRecordDecl* Abstract = findClass(Context, "Abstract");
    CXXRecordDecl* Concrete = findClass(Context, "Concrete");
    ASSERT_NE(Abstract, nullptr);
    ASSERT_NE(Concrete, nullptr);

    // Verify abstract detection
    EXPECT_TRUE(pureHandler.isAbstractClass(Abstract)) << "Abstract should be abstract";
    EXPECT_FALSE(pureHandler.isAbstractClass(Concrete)) << "Concrete should not be abstract";

    // Verify pure virtual detection
    auto pureVirtuals = pureHandler.getPureVirtualMethods(Abstract);
    EXPECT_EQ(pureVirtuals.size(), 1u) << "Should have 1 pure virtual method";
}

// Test 3: Virtual destructor
TEST_F(VirtualFunctionIntegrationTest, VirtualDestructor) {
    const char* code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() override {}
        };
    )";

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler destructorHandler(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT_NE(Base, nullptr);
    ASSERT_NE(Derived, nullptr);

    // Verify virtual destructor detection
    EXPECT_TRUE(destructorHandler.hasVirtualDestructor(Base))
        << "Base should have virtual destructor";
    EXPECT_TRUE(destructorHandler.hasVirtualDestructor(Derived))
        << "Derived should have virtual destructor";

    // Verify destructor should be first in vtable
    EXPECT_TRUE(destructorHandler.shouldDestructorBeFirstInVtable(Base))
        << "Destructor should be first in Base vtable";
}

// Test 4: Multiple overrides
TEST_F(VirtualFunctionIntegrationTest, MultipleOverrides) {
    const char* code = R"(
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

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT_NE(Base, nullptr);
    ASSERT_NE(Derived, nullptr);

    // Verify all methods are virtual
    auto baseMethods = analyzer.getVirtualMethods(Base);
    auto derivedMethods = analyzer.getVirtualMethods(Derived);
    EXPECT_EQ(baseMethods.size(), 3u) << "Base should have 3 virtual methods";
    EXPECT_EQ(derivedMethods.size(), 3u) << "Derived should have 3 virtual methods";

    // Verify override resolution
    auto vtableLayout = resolver.resolveVtableLayout(Derived);
    EXPECT_EQ(vtableLayout.size(), 3u) << "Vtable should have 3 slots";
}

// Test 5: Partial override
TEST_F(VirtualFunctionIntegrationTest, PartialOverride) {
    const char* code = R"(
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

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT_NE(Derived, nullptr);

    // Verify vtable has both methods
    auto vtableLayout = resolver.resolveVtableLayout(Derived);
    EXPECT_EQ(vtableLayout.size(), 2u) << "Vtable should have 2 slots";

    // Verify one is overridden, one is inherited
    int overriddenCount = 0;
    for (auto* method : vtableLayout) {
        if (method->getParent() == Derived) {
            overriddenCount++;
        }
    }
    EXPECT_EQ(overriddenCount, 1) << "Should have 1 overridden method";
}

// Test 6: Multi-level inheritance
TEST_F(VirtualFunctionIntegrationTest, MultiLevelInheritance) {
    const char* code = R"(
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

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Middle = findClass(Context, "Middle");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT_NE(Base, nullptr);
    ASSERT_NE(Middle, nullptr);
    ASSERT_NE(Derived, nullptr);

    // All should be polymorphic
    EXPECT_TRUE(analyzer.isPolymorphic(Base));
    EXPECT_TRUE(analyzer.isPolymorphic(Middle));
    EXPECT_TRUE(analyzer.isPolymorphic(Derived));

    // Verify vtable layout maintains consistency
    auto baseLayout = resolver.resolveVtableLayout(Base);
    auto middleLayout = resolver.resolveVtableLayout(Middle);
    auto derivedLayout = resolver.resolveVtableLayout(Derived);
    EXPECT_EQ(baseLayout.size(), middleLayout.size());
    EXPECT_EQ(middleLayout.size(), derivedLayout.size());
}

// Test 7: Polymorphic collection simulation
TEST_F(VirtualFunctionIntegrationTest, PolymorphicCollection) {
    const char* code = R"(
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

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Animal = findClass(Context, "Animal");
    CXXRecordDecl* Dog = findClass(Context, "Dog");
    CXXRecordDecl* Cat = findClass(Context, "Cat");
    ASSERT_NE(Animal, nullptr);
    ASSERT_NE(Dog, nullptr);
    ASSERT_NE(Cat, nullptr);

    // All should have compatible vtables
    auto animalMethods = resolver.resolveVtableLayout(Animal);
    auto dogMethods = resolver.resolveVtableLayout(Dog);
    auto catMethods = resolver.resolveVtableLayout(Cat);

    EXPECT_EQ(animalMethods.size(), dogMethods.size())
        << "Dog vtable should match Animal vtable size";
    EXPECT_EQ(animalMethods.size(), catMethods.size())
        << "Cat vtable should match Animal vtable size";
}

// Test 8: Upcast preserves virtual dispatch
TEST_F(VirtualFunctionIntegrationTest, UpcastPreservesDispatch) {
    const char* code = R"(
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

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualCallTranslator translator(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT_NE(Base, nullptr);
    ASSERT_NE(Derived, nullptr);

    // Verify both classes are polymorphic
    EXPECT_TRUE(analyzer.isPolymorphic(Base));
    EXPECT_TRUE(analyzer.isPolymorphic(Derived));

    // Both should have virtual methods
    auto baseMethods = analyzer.getVirtualMethods(Base);
    auto derivedMethods = analyzer.getVirtualMethods(Derived);
    EXPECT_FALSE(baseMethods.empty());
    EXPECT_FALSE(derivedMethods.empty());
}

// Test 9: Virtual call in constructor (detection)
TEST_F(VirtualFunctionIntegrationTest, VirtualCallInConstructor) {
    const char* code = R"(
        class Base {
        public:
            Base() {
                init();
            }
            virtual void init() {}
        };
    )";

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);

    CXXRecordDecl* Base = findClass(Context, "Base");
    ASSERT_NE(Base, nullptr);

    // Verify class is polymorphic
    EXPECT_TRUE(analyzer.isPolymorphic(Base));

    // Verify init is virtual
    auto virtualMethods = analyzer.getVirtualMethods(Base);
    bool hasInit = false;
    for (auto* method : virtualMethods) {
        if (method->getNameAsString() == "init") {
            hasInit = true;
            break;
        }
    }
    EXPECT_TRUE(hasInit) << "Should find virtual init method";
}

// Test 10: Vptr injection in polymorphic class
TEST_F(VirtualFunctionIntegrationTest, VptrInjection) {
    const char* code = R"(
        class Polymorphic {
        public:
            virtual void method() {}
        };
    )";

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VptrInjector injector(Context, analyzer);

    CXXRecordDecl* Polymorphic = findClass(Context, "Polymorphic");
    ASSERT_NE(Polymorphic, nullptr);

    // Verify class is polymorphic (vptr should be injected)
    EXPECT_TRUE(analyzer.isPolymorphic(Polymorphic))
        << "Should be polymorphic (needs vptr)";

    // Test vptr field injection
    vector<FieldDecl*> fields;
    bool injected = injector.injectVptrField(Polymorphic, fields);
    EXPECT_TRUE(injected) << "Should inject vptr";
    EXPECT_FALSE(fields.empty()) << "Should have vptr field";
}

// Test 11: Vtable initialization
TEST_F(VirtualFunctionIntegrationTest, VtableInitialization) {
    const char* code = R"(
        class MyClass {
        public:
            MyClass() {}
            virtual void method() {}
        };
    )";

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VtableInitializer initializer(Context, analyzer);

    CXXRecordDecl* MyClass = findClass(Context, "MyClass");
    ASSERT_NE(MyClass, nullptr);

    // Verify vtable name generation
    string vtableName = initializer.getVtableName(MyClass);
    EXPECT_EQ(vtableName, "__vtable_MyClass")
        << "Vtable name should be __vtable_MyClass";
}

// Test 12: Complex inheritance hierarchy
TEST_F(VirtualFunctionIntegrationTest, ComplexInheritance) {
    const char* code = R"(
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

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived1 = findClass(Context, "Derived1");
    CXXRecordDecl* Derived2 = findClass(Context, "Derived2");
    ASSERT_NE(Base, nullptr);
    ASSERT_NE(Derived1, nullptr);
    ASSERT_NE(Derived2, nullptr);

    // Verify all have proper vtable layouts
    auto baseLayout = resolver.resolveVtableLayout(Base);
    auto derived1Layout = resolver.resolveVtableLayout(Derived1);
    auto derived2Layout = resolver.resolveVtableLayout(Derived2);

    EXPECT_EQ(baseLayout.size(), 2u);
    EXPECT_EQ(derived1Layout.size(), 2u);
    EXPECT_EQ(derived2Layout.size(), 2u);
}

// Test 13: Abstract class with multiple pure virtuals
TEST_F(VirtualFunctionIntegrationTest, MultipleAbstractMethods) {
    const char* code = R"(
        class Interface {
        public:
            virtual void method1() = 0;
            virtual void method2() = 0;
            virtual void method3() = 0;
        };
    )";

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    PureVirtualHandler pureHandler(Context, analyzer);

    CXXRecordDecl* Interface = findClass(Context, "Interface");
    ASSERT_NE(Interface, nullptr);

    EXPECT_TRUE(pureHandler.isAbstractClass(Interface));

    auto pureVirtuals = pureHandler.getPureVirtualMethods(Interface);
    EXPECT_EQ(pureVirtuals.size(), 3u);
}

// Test 14: Virtual method signature matching
TEST_F(VirtualFunctionIntegrationTest, VirtualMethodSignatureMatching) {
    const char* code = R"(
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

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    OverrideResolver resolver(Context, analyzer);

    CXXRecordDecl* Base = findClass(Context, "Base");
    CXXRecordDecl* Derived = findClass(Context, "Derived");
    ASSERT_NE(Base, nullptr);
    ASSERT_NE(Derived, nullptr);

    // Both overloads should be in vtable
    auto baseLayout = resolver.resolveVtableLayout(Base);
    auto derivedLayout = resolver.resolveVtableLayout(Derived);
    EXPECT_EQ(baseLayout.size(), 2u);
    EXPECT_EQ(derivedLayout.size(), 2u);
}

// Test 15: Destructor chaining in hierarchy
TEST_F(VirtualFunctionIntegrationTest, DestructorChainingIntegration) {
    const char* code = R"(
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

    AST = buildAST(code);
    ASSERT_NE(AST, nullptr);

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler destructorHandler(Context, analyzer);

    CXXRecordDecl* A = findClass(Context, "A");
    CXXRecordDecl* B = findClass(Context, "B");
    CXXRecordDecl* C = findClass(Context, "C");
    ASSERT_NE(A, nullptr);
    ASSERT_NE(B, nullptr);
    ASSERT_NE(C, nullptr);

    // All should have virtual destructors
    EXPECT_TRUE(destructorHandler.hasVirtualDestructor(A));
    EXPECT_TRUE(destructorHandler.hasVirtualDestructor(B));
    EXPECT_TRUE(destructorHandler.hasVirtualDestructor(C));
}
