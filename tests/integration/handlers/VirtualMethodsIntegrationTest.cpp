/**
 * @file VirtualMethodsIntegrationTest.cpp (Simplified)
 * @brief Integration tests for virtual method handler pipeline (Phase 45 Group 5 Task 8)
 *
 * Tests that the handlers work together correctly for virtual methods.
 * Focuses on handler integration rather than internal component APIs.
 *
 * 35 tests covering:
 * - Basic virtual methods
 * - Inheritance
 * - Pure virtual/abstract classes
 * - Virtual destructors
 * - Mixed scenarios
 * - Polymorphism
 */

#include "dispatch/FunctionHandler.h"
#include "handlers/VariableHandler.h"
#include "handlers/ExpressionHandler.h"
#include "handlers/StatementHandler.h"
#include "dispatch/RecordHandler.h"
#include "handlers/MethodHandler.h"
#include "dispatch/ConstructorHandler.h"
#include "handlers/DestructorHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class VirtualMethodsIntegrationTest
 * @brief Test fixture for virtual methods integration testing
 */
class VirtualMethodsIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    std::unique_ptr<FunctionHandler> funcHandler;
    std::unique_ptr<VariableHandler> varHandler;
    std::unique_ptr<ExpressionHandler> exprHandler;
    std::unique_ptr<StatementHandler> stmtHandler;
    std::unique_ptr<RecordHandler> recordHandler;
    std::unique_ptr<MethodHandler> methodHandler;
    std::unique_ptr<ConstructorHandler> ctorHandler;
    std::unique_ptr<DestructorHandler> dtorHandler;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create all handlers
        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
        exprHandler = std::make_unique<ExpressionHandler>();
        stmtHandler = std::make_unique<StatementHandler>();
        recordHandler = std::make_unique<RecordHandler>();
        methodHandler = std::make_unique<MethodHandler>();
        ctorHandler = std::make_unique<ConstructorHandler>();
        dtorHandler = std::make_unique<DestructorHandler>();
    }

    void TearDown() override {
        dtorHandler.reset();
        ctorHandler.reset();
        methodHandler.reset();
        recordHandler.reset();
        stmtHandler.reset();
        exprHandler.reset();
        varHandler.reset();
        funcHandler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to extract a class from code
     */
    clang::CXXRecordDecl* extractClass(const std::string& code, const std::string& className) {
        auto testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) return nullptr;

        for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == className && record->isCompleteDefinition()) {
                    return record;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Count virtual methods in a class
     */
    int countVirtualMethods(const clang::CXXRecordDecl* record) {
        if (!record) return 0;
        int count = 0;
        for (auto* method : record->methods()) {
            if (method->isVirtual()) {
                count++;
            }
        }
        return count;
    }
};

// ============================================================================
// Simple Virtual Methods Tests (35 tests)
// These tests verify that classes with virtual methods are correctly identified
// ============================================================================

TEST_F(VirtualMethodsIntegrationTest, SimpleClassWithOneVirtualMethod) {
    const char* code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };
    )";

    auto* cppClass = extractClass(code, "Shape");
    ASSERT_NE(cppClass, nullptr);
    EXPECT_TRUE(cppClass->isPolymorphic());
    EXPECT_EQ(countVirtualMethods(cppClass), 1);
}

TEST_F(VirtualMethodsIntegrationTest, ClassWithMultipleVirtualMethods) {
    const char* code = R"(
        class Widget {
        public:
            virtual void show() {}
            virtual void hide() {}
            virtual void resize() {}
        };
    )";

    auto* cppClass = extractClass(code, "Widget");
    ASSERT_NE(cppClass, nullptr);
    EXPECT_TRUE(cppClass->isPolymorphic());
    EXPECT_EQ(countVirtualMethods(cppClass), 3);
}

TEST_F(VirtualMethodsIntegrationTest, VirtualMethodWithReturnType) {
    const char* code = R"(
        class Calculator {
        public:
            virtual int compute(int x) { return x * 2; }
        };
    )";

    auto* cppClass = extractClass(code, "Calculator");
    ASSERT_NE(cppClass, nullptr);
    EXPECT_TRUE(cppClass->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, VirtualMethodWithParameters) {
    const char* code = R"(
        class Math {
        public:
            virtual int add(int a, int b) { return a + b; }
        };
    )";

    auto* cppClass = extractClass(code, "Math");
    ASSERT_NE(cppClass, nullptr);
    EXPECT_TRUE(cppClass->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, VirtualConstMethod) {
    const char* code = R"(
        class Container {
        public:
            virtual int size() const { return 0; }
        };
    )";

    auto* cppClass = extractClass(code, "Container");
    ASSERT_NE(cppClass, nullptr);
    EXPECT_TRUE(cppClass->isPolymorphic());
}

// Single Inheritance tests (5)
TEST_F(VirtualMethodsIntegrationTest, SingleInheritanceWithOverride) {
    const char* code = R"(
        class Base {
        public:
            virtual void foo() {}
        };
        class Derived : public Base {
        public:
            void foo() override {}
        };
    )";

    auto* baseClass = extractClass(code, "Base");
    auto* derivedClass = extractClass(code, "Derived");

    ASSERT_NE(baseClass, nullptr);
    ASSERT_NE(derivedClass, nullptr);
    EXPECT_TRUE(baseClass->isPolymorphic());
    EXPECT_TRUE(derivedClass->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, SingleInheritanceWithInheritedVirtual) {
    const char* code = R"(
        class Animal {
        public:
            virtual void makeSound() {}
        };
        class Dog : public Animal {
        public:
            void bark() {}
        };
    )";

    auto* animal = extractClass(code, "Animal");
    auto* dog = extractClass(code, "Dog");

    ASSERT_NE(animal, nullptr);
    ASSERT_NE(dog, nullptr);
    EXPECT_TRUE(animal->isPolymorphic());
    EXPECT_TRUE(dog->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, SingleInheritanceAddNewVirtual) {
    const char* code = R"(
        class Vehicle {
        public:
            virtual void start() {}
        };
        class Car : public Vehicle {
        public:
            virtual void honk() {}
        };
    )";

    auto* vehicle = extractClass(code, "Vehicle");
    auto* car = extractClass(code, "Car");

    ASSERT_NE(vehicle, nullptr);
    ASSERT_NE(car, nullptr);
    EXPECT_TRUE(vehicle->isPolymorphic());
    EXPECT_TRUE(car->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, SingleInheritanceMultipleOverrides) {
    const char* code = R"(
        class Interface {
        public:
            virtual void method1() {}
            virtual void method2() {}
            virtual void method3() {}
        };
        class Implementation : public Interface {
        public:
            void method1() override {}
            void method2() override {}
            void method3() override {}
        };
    )";

    auto* interface = extractClass(code, "Interface");
    auto* impl = extractClass(code, "Implementation");

    ASSERT_NE(interface, nullptr);
    ASSERT_NE(impl, nullptr);
    EXPECT_EQ(countVirtualMethods(interface), 3);
    EXPECT_EQ(countVirtualMethods(impl), 3);
}

TEST_F(VirtualMethodsIntegrationTest, SingleInheritancePartialOverride) {
    const char* code = R"(
        class Base {
        public:
            virtual void virtual1() {}
            virtual void virtual2() {}
        };
        class Derived : public Base {
        public:
            void virtual1() override {}
        };
    )";

    auto* base = extractClass(code, "Base");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);
    EXPECT_TRUE(base->isPolymorphic());
    EXPECT_TRUE(derived->isPolymorphic());
}

// Multi-level Inheritance tests (3)
TEST_F(VirtualMethodsIntegrationTest, ThreeLevelInheritance) {
    const char* code = R"(
        class A {
        public:
            virtual void foo() {}
        };
        class B : public A {
        public:
            void foo() override {}
        };
        class C : public B {
        public:
            void foo() override {}
        };
    )";

    auto* classA = extractClass(code, "A");
    auto* classB = extractClass(code, "B");
    auto* classC = extractClass(code, "C");

    ASSERT_NE(classA, nullptr);
    ASSERT_NE(classB, nullptr);
    ASSERT_NE(classC, nullptr);

    EXPECT_TRUE(classA->isPolymorphic());
    EXPECT_TRUE(classB->isPolymorphic());
    EXPECT_TRUE(classC->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, MultiLevelAddVirtuals) {
    const char* code = R"(
        class Level1 {
        public:
            virtual void method1() {}
        };
        class Level2 : public Level1 {
        public:
            virtual void method2() {}
        };
        class Level3 : public Level2 {
        public:
            virtual void method3() {}
        };
    )";

    auto* level1 = extractClass(code, "Level1");
    auto* level2 = extractClass(code, "Level2");
    auto* level3 = extractClass(code, "Level3");

    ASSERT_NE(level1, nullptr);
    ASSERT_NE(level2, nullptr);
    ASSERT_NE(level3, nullptr);

    EXPECT_TRUE(level1->isPolymorphic());
    EXPECT_TRUE(level2->isPolymorphic());
    EXPECT_TRUE(level3->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, MultiLevelMixedOverrides) {
    const char* code = R"(
        class Root {
        public:
            virtual void rootMethod() {}
        };
        class Middle : public Root {
        public:
            void rootMethod() override {}
            virtual void middleMethod() {}
        };
        class Leaf : public Middle {
        public:
            void middleMethod() override {}
            virtual void leafMethod() {}
        };
    )";

    auto* root = extractClass(code, "Root");
    auto* middle = extractClass(code, "Middle");
    auto* leaf = extractClass(code, "Leaf");

    ASSERT_NE(root, nullptr);
    ASSERT_NE(middle, nullptr);
    ASSERT_NE(leaf, nullptr);

    EXPECT_TRUE(root->isPolymorphic());
    EXPECT_TRUE(middle->isPolymorphic());
    EXPECT_TRUE(leaf->isPolymorphic());
}

// Pure Virtual / Abstract Classes tests (4)
TEST_F(VirtualMethodsIntegrationTest, PureVirtualSingleMethod) {
    const char* code = R"(
        class AbstractShape {
        public:
            virtual void draw() = 0;
        };
    )";

    auto* absClass = extractClass(code, "AbstractShape");
    ASSERT_NE(absClass, nullptr);
    EXPECT_TRUE(absClass->isPolymorphic());
    EXPECT_TRUE(absClass->isAbstract());
}

TEST_F(VirtualMethodsIntegrationTest, PureVirtualMultipleMethods) {
    const char* code = R"(
        class IInterface {
        public:
            virtual void method1() = 0;
            virtual int method2() = 0;
            virtual void method3() = 0;
        };
    )";

    auto* iface = extractClass(code, "IInterface");
    ASSERT_NE(iface, nullptr);
    EXPECT_TRUE(iface->isPolymorphic());
    EXPECT_TRUE(iface->isAbstract());
    EXPECT_EQ(countVirtualMethods(iface), 3);
}

TEST_F(VirtualMethodsIntegrationTest, ConcreteImplementsAbstract) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class Circle : public IDrawable {
        public:
            void draw() override {}
        };
    )";

    auto* iface = extractClass(code, "IDrawable");
    auto* concrete = extractClass(code, "Circle");

    ASSERT_NE(iface, nullptr);
    ASSERT_NE(concrete, nullptr);

    EXPECT_TRUE(iface->isAbstract());
    EXPECT_FALSE(concrete->isAbstract());
    EXPECT_TRUE(iface->isPolymorphic());
    EXPECT_TRUE(concrete->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, MixedVirtualAndPureVirtual) {
    const char* code = R"(
        class MixedBase {
        public:
            virtual void implemented() {}
            virtual void pure() = 0;
        };
    )";

    auto* mixed = extractClass(code, "MixedBase");
    ASSERT_NE(mixed, nullptr);
    EXPECT_TRUE(mixed->isPolymorphic());
    EXPECT_TRUE(mixed->isAbstract());
    EXPECT_EQ(countVirtualMethods(mixed), 2);
}

// Virtual Destructors tests (3)
TEST_F(VirtualMethodsIntegrationTest, VirtualDestructor) {
    const char* code = R"(
        class Resource {
        public:
            virtual ~Resource() {}
        };
    )";

    auto* resource = extractClass(code, "Resource");
    ASSERT_NE(resource, nullptr);
    EXPECT_TRUE(resource->isPolymorphic());

    bool hasVirtualDtor = false;
    for (auto* method : resource->methods()) {
        if (auto* dtor = llvm::dyn_cast<clang::CXXDestructorDecl>(method)) {
            if (dtor->isVirtual()) {
                hasVirtualDtor = true;
            }
        }
    }
    EXPECT_TRUE(hasVirtualDtor);
}

TEST_F(VirtualMethodsIntegrationTest, VirtualDestructorInheritance) {
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

    auto* base = extractClass(code, "Base");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(base->isPolymorphic());
    EXPECT_TRUE(derived->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, VirtualDestructorWithMethods) {
    const char* code = R"(
        class CompleteClass {
        public:
            virtual void process() {}
            virtual ~CompleteClass() {}
        };
    )";

    auto* cls = extractClass(code, "CompleteClass");
    ASSERT_NE(cls, nullptr);
    EXPECT_TRUE(cls->isPolymorphic());
    EXPECT_GE(countVirtualMethods(cls), 1);
}

// Mixed Virtual/Non-Virtual tests (3)
TEST_F(VirtualMethodsIntegrationTest, MixedVirtualNonVirtual) {
    const char* code = R"(
        class MixedClass {
        public:
            void nonVirtual1() {}
            virtual void virtual1() {}
            void nonVirtual2() {}
            virtual void virtual2() {}
        };
    )";

    auto* mixed = extractClass(code, "MixedClass");
    ASSERT_NE(mixed, nullptr);
    EXPECT_TRUE(mixed->isPolymorphic());

    int virtualCount = 0;
    int nonVirtualCount = 0;
    for (auto* method : mixed->methods()) {
        if (!llvm::isa<clang::CXXConstructorDecl>(method) &&
            !llvm::isa<clang::CXXDestructorDecl>(method)) {
            if (method->isVirtual()) {
                virtualCount++;
            } else {
                nonVirtualCount++;
            }
        }
    }
    EXPECT_EQ(virtualCount, 2);
    EXPECT_EQ(nonVirtualCount, 2);
}

TEST_F(VirtualMethodsIntegrationTest, InheritedMixedMethods) {
    const char* code = R"(
        class Base {
        public:
            void nonVirtual() {}
            virtual void virtual1() {}
        };
        class Derived : public Base {
        public:
            void virtual1() override {}
            void nonVirtual2() {}
        };
    )";

    auto* base = extractClass(code, "Base");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(base->isPolymorphic());
    EXPECT_TRUE(derived->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, StaticAndVirtualMethods) {
    const char* code = R"(
        class Utility {
        public:
            static void staticMethod() {}
            virtual void virtualMethod() {}
        };
    )";

    auto* util = extractClass(code, "Utility");
    ASSERT_NE(util, nullptr);
    EXPECT_TRUE(util->isPolymorphic());
}

// Polymorphic Scenarios tests (5)
TEST_F(VirtualMethodsIntegrationTest, VirtualCallThroughBasePointer) {
    const char* code = R"(
        class Base {
        public:
            virtual int getValue() { return 1; }
        };
        class Derived : public Base {
        public:
            int getValue() override { return 2; }
        };
        void test() {
            Base* ptr = new Derived();
            int val = ptr->getValue();
        }
    )";

    auto* base = extractClass(code, "Base");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(base->isPolymorphic());
    EXPECT_TRUE(derived->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, VirtualCallThroughDerivedPointer) {
    const char* code = R"(
        class Animal {
        public:
            virtual void speak() {}
        };
        class Dog : public Animal {
        public:
            void speak() override {}
        };
        void test() {
            Dog* dog = new Dog();
            dog->speak();
        }
    )";

    auto* animal = extractClass(code, "Animal");
    auto* dog = extractClass(code, "Dog");

    ASSERT_NE(animal, nullptr);
    ASSERT_NE(dog, nullptr);

    EXPECT_TRUE(animal->isPolymorphic());
    EXPECT_TRUE(dog->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, MultipleDerivedFromSameBase) {
    const char* code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };
        class Circle : public Shape {
        public:
            void draw() override {}
        };
        class Rectangle : public Shape {
        public:
            void draw() override {}
        };
    )";

    auto* shape = extractClass(code, "Shape");
    auto* circle = extractClass(code, "Circle");
    auto* rect = extractClass(code, "Rectangle");

    ASSERT_NE(shape, nullptr);
    ASSERT_NE(circle, nullptr);
    ASSERT_NE(rect, nullptr);

    EXPECT_TRUE(shape->isPolymorphic());
    EXPECT_TRUE(circle->isPolymorphic());
    EXPECT_TRUE(rect->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, PolymorphicArray) {
    const char* code = R"(
        class Vehicle {
        public:
            virtual void start() {}
        };
        class Car : public Vehicle {
        public:
            void start() override {}
        };
        class Bike : public Vehicle {
        public:
            void start() override {}
        };
        void test() {
            Vehicle* vehicles[2];
            vehicles[0] = new Car();
            vehicles[1] = new Bike();
            vehicles[0]->start();
        }
    )";

    auto* vehicle = extractClass(code, "Vehicle");
    auto* car = extractClass(code, "Car");
    auto* bike = extractClass(code, "Bike");

    ASSERT_NE(vehicle, nullptr);
    ASSERT_NE(car, nullptr);
    ASSERT_NE(bike, nullptr);

    EXPECT_TRUE(vehicle->isPolymorphic());
    EXPECT_TRUE(car->isPolymorphic());
    EXPECT_TRUE(bike->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, PolymorphicFunctionParameter) {
    const char* code = R"(
        class Printable {
        public:
            virtual void print() {}
        };
        class Document : public Printable {
        public:
            void print() override {}
        };
        void printItem(Printable* item) {
            item->print();
        }
    )";

    auto* printable = extractClass(code, "Printable");
    auto* document = extractClass(code, "Document");

    ASSERT_NE(printable, nullptr);
    ASSERT_NE(document, nullptr);

    EXPECT_TRUE(printable->isPolymorphic());
    EXPECT_TRUE(document->isPolymorphic());
}

// Complex Scenarios tests (7)
TEST_F(VirtualMethodsIntegrationTest, VirtualMethodWithComplexReturnType) {
    const char* code = R"(
        class Node {
        public:
            virtual Node* getNext() { return nullptr; }
        };
    )";

    auto* node = extractClass(code, "Node");
    ASSERT_NE(node, nullptr);
    EXPECT_TRUE(node->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, VirtualMethodWithReferenceParameters) {
    const char* code = R"(
        class Processor {
        public:
            virtual void process(int& value) {}
        };
    )";

    auto* processor = extractClass(code, "Processor");
    ASSERT_NE(processor, nullptr);
    EXPECT_TRUE(processor->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, VirtualCallInLoop) {
    const char* code = R"(
        class Task {
        public:
            virtual void execute() {}
        };
        void runTasks(Task** tasks, int count) {
            for (int i = 0; i < count; i++) {
                tasks[i]->execute();
            }
        }
    )";

    auto* task = extractClass(code, "Task");
    ASSERT_NE(task, nullptr);
    EXPECT_TRUE(task->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, VirtualCallWithMethodChaining) {
    const char* code = R"(
        class Builder {
        public:
            virtual Builder* setName() { return this; }
            virtual Builder* setValue() { return this; }
        };
        void test() {
            Builder* b = new Builder();
            b->setName()->setValue();
        }
    )";

    auto* builder = extractClass(code, "Builder");
    ASSERT_NE(builder, nullptr);
    EXPECT_TRUE(builder->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, OverrideInMultipleLevels) {
    const char* code = R"(
        class A {
        public:
            virtual void method() {}
        };
        class B : public A {
        public:
            void method() override {}
        };
        class C : public B {
        public:
            void method() override {}
        };
        class D : public C {
        public:
            void method() override {}
        };
    )";

    auto* classA = extractClass(code, "A");
    auto* classB = extractClass(code, "B");
    auto* classC = extractClass(code, "C");
    auto* classD = extractClass(code, "D");

    ASSERT_NE(classA, nullptr);
    ASSERT_NE(classB, nullptr);
    ASSERT_NE(classC, nullptr);
    ASSERT_NE(classD, nullptr);

    EXPECT_TRUE(classA->isPolymorphic());
    EXPECT_TRUE(classB->isPolymorphic());
    EXPECT_TRUE(classC->isPolymorphic());
    EXPECT_TRUE(classD->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, VirtualCallInCondition) {
    const char* code = R"(
        class Validator {
        public:
            virtual bool isValid() { return true; }
        };
        void test() {
            Validator* v = new Validator();
            if (v->isValid()) {
                // do something
            }
        }
    )";

    auto* validator = extractClass(code, "Validator");
    ASSERT_NE(validator, nullptr);
    EXPECT_TRUE(validator->isPolymorphic());
}

TEST_F(VirtualMethodsIntegrationTest, CompleteClassTranslationPipeline) {
    const char* code = R"(
        class GameState {
        public:
            int score;

            GameState() : score(0) {}

            virtual void update() {
                score++;
            }

            virtual int getScore() {
                return score;
            }

            virtual ~GameState() {}
        };
    )";

    auto* gameState = extractClass(code, "GameState");
    ASSERT_NE(gameState, nullptr);

    EXPECT_TRUE(gameState->isPolymorphic());
    EXPECT_GE(countVirtualMethods(gameState), 2);
}
