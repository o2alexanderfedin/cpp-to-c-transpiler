/**
 * @file VirtualMethodsE2ETest.cpp
 * @brief End-to-end tests for virtual methods with COM-style vtables (Phase 45 Group 5 Task 9)
 *
 * Tests the complete pipeline with Phase 45 features:
 * Stage 1: Clang parses C++ → C++ AST
 * Stage 2: Handlers translate C++ AST → C AST (with virtual methods)
 * Stage 3: CodeGenerator emits C source (with vtable dispatch)
 * Validation: Compile C code with gcc and execute
 *
 * Test Strategy:
 * - 1 active sanity test (simple virtual call)
 * - 2-3 active tests (basic polymorphism)
 * - 10-12 disabled tests (complex patterns for future)
 */

#include "handlers/FunctionHandler.h"
#include "handlers/VariableHandler.h"
#include "handlers/ExpressionHandler.h"
#include "handlers/StatementHandler.h"
#include "handlers/RecordHandler.h"
#include "handlers/MethodHandler.h"
#include "handlers/ConstructorHandler.h"
#include "handlers/DestructorHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "CodeGenerator.h"
#include "VirtualMethodAnalyzer.h"
#include "VtableGenerator.h"
#include "VptrInjector.h"
#include "VtableInitializer.h"
#include "VirtualCallTranslator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>
#include <fstream>
#include <cstdlib>

using namespace cpptoc;

/**
 * @class VirtualMethodsE2ETest
 * @brief Test fixture for end-to-end virtual methods testing
 */
class VirtualMethodsE2ETest : public ::testing::Test {
protected:
    std::unique_ptr<FunctionHandler> funcHandler;
    std::unique_ptr<VariableHandler> varHandler;
    std::unique_ptr<ExpressionHandler> exprHandler;
    std::unique_ptr<StatementHandler> stmtHandler;
    std::unique_ptr<RecordHandler> recordHandler;
    std::unique_ptr<MethodHandler> methodHandler;
    std::unique_ptr<ConstructorHandler> ctorHandler;
    std::unique_ptr<DestructorHandler> dtorHandler;

    void SetUp() override {
        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
        exprHandler = std::make_unique<ExpressionHandler>();
        stmtHandler = std::make_unique<StatementHandler>();
        recordHandler = std::make_unique<RecordHandler>();
        methodHandler = std::make_unique<MethodHandler>();
        ctorHandler = std::make_unique<ConstructorHandler>();
        dtorHandler = std::make_unique<DestructorHandler>();
    }

    /**
     * @brief Run complete pipeline: C++ source → C source → compile → execute
     * @param cppCode C++ source code
     * @param expectedExitCode Expected exit code from execution
     * @param debugOutput If true, print generated C code
     * @return true if test passed
     */
    bool runPipeline(const std::string& cppCode, int expectedExitCode, bool debugOutput = false) {
        // Stage 1: Parse C++ code
        auto cppAST = clang::tooling::buildASTFromCode(cppCode);
        if (!cppAST) {
            std::cerr << "Failed to parse C++ code\n";
            return false;
        }

        // Stage 2: Translate to C AST
        auto cAST = clang::tooling::buildASTFromCode("int dummy;");
        if (!cAST) {
            std::cerr << "Failed to create C context\n";
            return false;
        }

        clang::CNodeBuilder builder(cAST->getASTContext());
        HandlerContext context(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            builder
        );

        // Create virtual method infrastructure
        VirtualMethodAnalyzer virtualAnalyzer(cppAST->getASTContext());
        VtableGenerator vtableGen(cAST->getASTContext(), builder);
        VptrInjector vptrInjector(cAST->getASTContext());
        VtableInitializer vtableInit(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            builder
        );
        VirtualCallTranslator virtualCallTrans(
            cppAST->getASTContext(),
            virtualAnalyzer
        );

        // Phase 1: Analyze virtual methods in all classes
        for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (cxxRecord->isCompleteDefinition()) {
                    // Analysis happens automatically via isPolymorphic()
                }
            }
        }

        // Phase 2: Translate all declarations
        for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (cxxRecord->isCompleteDefinition()) {
                    // Translate class to struct
                    auto* cRecord = llvm::dyn_cast<clang::RecordDecl>(
                        recordHandler->handleDecl(llvm::cast<clang::RecordDecl>(cxxRecord), context)
                    );

                    // If class has virtual methods, generate vtable and inject vptr
                    if (cRecord && virtualAnalyzer.isPolymorphic(cxxRecord)) {
                        auto* vtableStruct = vtableGen.generateVtableStruct(cxxRecord, virtualAnalyzer);
                        if (vtableStruct) {
                            vptrInjector.injectVptr(cRecord, vtableStruct);
                        }
                    }

                    // Handle methods, constructors, destructors
                    for (auto* member : cxxRecord->decls()) {
                        if (auto* ctor = llvm::dyn_cast<clang::CXXConstructorDecl>(member)) {
                            auto* cCtor = ctorHandler->handleDecl(ctor, context);
                            // Initialize vtable in constructor if class has virtuals
                            if (cCtor && virtualAnalyzer.isPolymorphic(cxxRecord)) {
                                vtableInit.initializeVtableInConstructor(
                                    llvm::cast<clang::FunctionDecl>(cCtor),
                                    cxxRecord,
                                    virtualAnalyzer
                                );
                            }
                        } else if (auto* dtor = llvm::dyn_cast<clang::CXXDestructorDecl>(member)) {
                            dtorHandler->handleDecl(dtor, context);
                        } else if (auto* method = llvm::dyn_cast<clang::CXXMethodDecl>(member)) {
                            if (!llvm::isa<clang::CXXConstructorDecl>(method) &&
                                !llvm::isa<clang::CXXDestructorDecl>(method)) {
                                methodHandler->handleDecl(method, context);
                            }
                        }
                    }
                }
            } else if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
                if (!llvm::isa<clang::CXXMethodDecl>(func)) {
                    funcHandler->handleDecl(func, context);
                }
            }
        }

        // Stage 3: Generate C code
        std::string cCode;
        llvm::raw_string_ostream codeStream(cCode);
        CodeGenerator generator(codeStream, cAST->getASTContext());
        generator.printTranslationUnit(cAST->getASTContext().getTranslationUnitDecl());
        codeStream.flush();

        if (debugOutput) {
            std::cout << "=== Generated C Code ===\n" << cCode << "\n========================\n";
        }

        // Write C code to temporary file
        std::string tmpFile = "/tmp/e2e_virtual_test_" + std::to_string(rand()) + ".c";
        std::ofstream outFile(tmpFile);
        outFile << cCode;
        outFile.close();

        // Compile with gcc
        std::string compileCmd = "gcc -std=c99 " + tmpFile + " -o " + tmpFile + ".out 2>&1";
        int compileResult = system(compileCmd.c_str());
        if (compileResult != 0) {
            std::cerr << "Compilation failed\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            system(("cat " + tmpFile).c_str());
            return false;
        }

        // Execute
        std::string execCmd = tmpFile + ".out";
        int execResult = system(execCmd.c_str());
        int actualExitCode = WEXITSTATUS(execResult);

        // Cleanup
        system(("rm -f " + tmpFile + " " + tmpFile + ".out").c_str());

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// ACTIVE E2E Tests (1-3 tests)
// ============================================================================

/**
 * E2E Test 1: Simple Virtual Call (ACTIVE SANITY TEST)
 *
 * Tests basic virtual method call with COM-style vtable dispatch.
 * Expected C translation pattern:
 * - Shape struct with lpVtbl pointer
 * - Shape_vtable struct with draw function pointer
 * - Shape_draw(Shape* this) implementation
 * - Constructor initializes lpVtbl
 * - Call: shape->lpVtbl->draw(shape)
 */
TEST_F(VirtualMethodsE2ETest, SimpleVirtualCall) {
    std::string cppCode = R"(
        class Shape {
        public:
            int value;

            Shape() {
                value = 42;
            }

            virtual int getValue() {
                return value;
            }
        };

        int main() {
            Shape s;
            return s.getValue();  // Returns 42
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 42, true)) << "Expected exit code 42";
}

/**
 * E2E Test 2: Polymorphic Function Call (ACTIVE)
 *
 * Tests polymorphism with base and derived classes.
 * Base* ptr points to Derived instance.
 * Virtual call through base pointer should invoke derived implementation.
 */
TEST_F(VirtualMethodsE2ETest, PolymorphicFunctionCall) {
    std::string cppCode = R"(
        class Base {
        public:
            virtual int getValue() {
                return 1;
            }
        };

        class Derived : public Base {
        public:
            int getValue() override {
                return 2;
            }
        };

        int test(Base* ptr) {
            return ptr->getValue();
        }

        int main() {
            Derived d;
            Base* ptr = &d;
            return test(ptr);  // Should return 2 (derived implementation)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 2, true)) << "Expected exit code 2 (polymorphic call)";
}

/**
 * E2E Test 3: Multiple Virtual Methods (ACTIVE)
 *
 * Tests class with multiple virtual methods.
 * Verifies vtable has correct function pointers for all methods.
 */
TEST_F(VirtualMethodsE2ETest, MultipleVirtualMethods) {
    std::string cppCode = R"(
        class Calculator {
        public:
            virtual int add(int a, int b) {
                return a + b;
            }

            virtual int multiply(int a, int b) {
                return a * b;
            }
        };

        int main() {
            Calculator calc;
            int sum = calc.add(3, 4);        // 7
            int product = calc.multiply(2, 3); // 6
            return sum + product;  // Returns 13
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 13, true)) << "Expected exit code 13 (7 + 6)";
}

// ============================================================================
// DISABLED E2E Tests (12 tests for future implementation)
// ============================================================================

/**
 * E2E Test 4: Shape Hierarchy (Circle, Rectangle) - DISABLED
 *
 * Classic polymorphism example with geometric shapes.
 * Tests inheritance, virtual method override, and polymorphic array.
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_ShapeHierarchy) {
    std::string cppCode = R"(
        class Shape {
        public:
            virtual int area() = 0;
        };

        class Circle : public Shape {
        public:
            int radius;
            Circle() : radius(5) {}
            int area() override {
                return 3 * radius * radius;  // Approximate pi as 3
            }
        };

        class Rectangle : public Shape {
        public:
            int width;
            int height;
            Rectangle() : width(4), height(6) {}
            int area() override {
                return width * height;
            }
        };

        int main() {
            Circle c;
            Rectangle r;
            Shape* shapes[2];
            shapes[0] = &c;
            shapes[1] = &r;
            return shapes[0]->area() + shapes[1]->area();  // 75 + 24 = 99
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 99)) << "Expected exit code 99";
}

/**
 * E2E Test 5: Animal Hierarchy (Dog, Cat) - DISABLED
 *
 * Tests polymorphism with animal sounds.
 * Multiple derived classes from same base.
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_AnimalHierarchy) {
    std::string cppCode = R"(
        class Animal {
        public:
            virtual int getSound() = 0;
        };

        class Dog : public Animal {
        public:
            int getSound() override {
                return 1;  // Bark = 1
            }
        };

        class Cat : public Animal {
        public:
            int getSound() override {
                return 2;  // Meow = 2
            }
        };

        int main() {
            Dog d;
            Cat c;
            Animal* animals[2];
            animals[0] = &d;
            animals[1] = &c;
            return animals[0]->getSound() + animals[1]->getSound();  // 1 + 2 = 3
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 3)) << "Expected exit code 3";
}

/**
 * E2E Test 6: Stack Interface with Implementations - DISABLED
 *
 * Tests interface (pure virtual) with concrete implementations.
 * Array-based stack and linked-list stack.
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_StackInterface) {
    std::string cppCode = R"(
        class IStack {
        public:
            virtual void push(int value) = 0;
            virtual int pop() = 0;
            virtual bool isEmpty() = 0;
        };

        class ArrayStack : public IStack {
        private:
            int data[10];
            int top;
        public:
            ArrayStack() : top(-1) {}
            void push(int value) override {
                if (top < 9) data[++top] = value;
            }
            int pop() override {
                return (top >= 0) ? data[top--] : 0;
            }
            bool isEmpty() override {
                return top < 0;
            }
        };

        int main() {
            ArrayStack stack;
            stack.push(10);
            stack.push(20);
            stack.push(30);
            int a = stack.pop();  // 30
            int b = stack.pop();  // 20
            return a + b;  // Returns 50
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 50)) << "Expected exit code 50";
}

/**
 * E2E Test 7: List Interface with Implementations - DISABLED
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_ListInterface) {
    std::string cppCode = R"(
        class IList {
        public:
            virtual void add(int value) = 0;
            virtual int get(int index) = 0;
            virtual int size() = 0;
        };

        class ArrayList : public IList {
        private:
            int data[10];
            int count;
        public:
            ArrayList() : count(0) {}
            void add(int value) override {
                if (count < 10) data[count++] = value;
            }
            int get(int index) override {
                return (index >= 0 && index < count) ? data[index] : 0;
            }
            int size() override {
                return count;
            }
        };

        int main() {
            ArrayList list;
            list.add(5);
            list.add(10);
            list.add(15);
            return list.get(0) + list.get(1) + list.get(2);  // 5 + 10 + 15 = 30
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 30)) << "Expected exit code 30";
}

/**
 * E2E Test 8: Iterator Pattern - DISABLED
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_IteratorPattern) {
    std::string cppCode = R"(
        class Iterator {
        public:
            virtual bool hasNext() = 0;
            virtual int next() = 0;
        };

        class ArrayIterator : public Iterator {
        private:
            int* array;
            int size;
            int current;
        public:
            ArrayIterator(int* arr, int sz) : array(arr), size(sz), current(0) {}
            bool hasNext() override {
                return current < size;
            }
            int next() override {
                return array[current++];
            }
        };

        int main() {
            int data[] = {1, 2, 3, 4, 5};
            ArrayIterator it(data, 5);
            int sum = 0;
            while (it.hasNext()) {
                sum += it.next();
            }
            return sum;  // Returns 15
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 15)) << "Expected exit code 15";
}

/**
 * E2E Test 9: Strategy Pattern - DISABLED
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_StrategyPattern) {
    std::string cppCode = R"(
        class Strategy {
        public:
            virtual int execute(int a, int b) = 0;
        };

        class AddStrategy : public Strategy {
        public:
            int execute(int a, int b) override {
                return a + b;
            }
        };

        class MultiplyStrategy : public Strategy {
        public:
            int execute(int a, int b) override {
                return a * b;
            }
        };

        class Context {
        private:
            Strategy* strategy;
        public:
            void setStrategy(Strategy* s) {
                strategy = s;
            }
            int executeStrategy(int a, int b) {
                return strategy->execute(a, b);
            }
        };

        int main() {
            AddStrategy add;
            MultiplyStrategy multiply;
            Context ctx;

            ctx.setStrategy(&add);
            int result1 = ctx.executeStrategy(3, 4);  // 7

            ctx.setStrategy(&multiply);
            int result2 = ctx.executeStrategy(3, 4);  // 12

            return result1 + result2;  // Returns 19
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 19)) << "Expected exit code 19";
}

/**
 * E2E Test 10: Observer Pattern - DISABLED
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_ObserverPattern) {
    std::string cppCode = R"(
        class Observer {
        public:
            virtual void update(int value) = 0;
        };

        class ConcreteObserver : public Observer {
        private:
            int state;
        public:
            ConcreteObserver() : state(0) {}
            void update(int value) override {
                state = value;
            }
            int getState() {
                return state;
            }
        };

        class Subject {
        private:
            Observer* observers[5];
            int observerCount;
            int state;
        public:
            Subject() : observerCount(0), state(0) {}
            void attach(Observer* obs) {
                if (observerCount < 5) observers[observerCount++] = obs;
            }
            void setState(int value) {
                state = value;
                notify();
            }
            void notify() {
                for (int i = 0; i < observerCount; i++) {
                    observers[i]->update(state);
                }
            }
        };

        int main() {
            Subject subject;
            ConcreteObserver obs1;
            ConcreteObserver obs2;

            subject.attach(&obs1);
            subject.attach(&obs2);
            subject.setState(42);

            return obs1.getState() + obs2.getState();  // 42 + 42 = 84
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 84)) << "Expected exit code 84";
}

/**
 * E2E Test 11: Factory Pattern - DISABLED
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_FactoryPattern) {
    std::string cppCode = R"(
        class Product {
        public:
            virtual int getValue() = 0;
        };

        class ProductA : public Product {
        public:
            int getValue() override {
                return 10;
            }
        };

        class ProductB : public Product {
        public:
            int getValue() override {
                return 20;
            }
        };

        class Factory {
        public:
            static Product* createProduct(int type) {
                static ProductA a;
                static ProductB b;
                if (type == 1) return &a;
                else return &b;
            }
        };

        int main() {
            Product* p1 = Factory::createProduct(1);
            Product* p2 = Factory::createProduct(2);
            return p1->getValue() + p2->getValue();  // 10 + 20 = 30
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 30)) << "Expected exit code 30";
}

/**
 * E2E Test 12: Plugin System - DISABLED
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_PluginSystem) {
    std::string cppCode = R"(
        class Plugin {
        public:
            virtual int process(int input) = 0;
        };

        class DoublePlugin : public Plugin {
        public:
            int process(int input) override {
                return input * 2;
            }
        };

        class SquarePlugin : public Plugin {
        public:
            int process(int input) override {
                return input * input;
            }
        };

        class PluginManager {
        private:
            Plugin* plugins[10];
            int pluginCount;
        public:
            PluginManager() : pluginCount(0) {}
            void registerPlugin(Plugin* p) {
                if (pluginCount < 10) plugins[pluginCount++] = p;
            }
            int processAll(int input) {
                int result = input;
                for (int i = 0; i < pluginCount; i++) {
                    result = plugins[i]->process(result);
                }
                return result;
            }
        };

        int main() {
            PluginManager manager;
            DoublePlugin doubler;
            SquarePlugin squarer;

            manager.registerPlugin(&doubler);
            manager.registerPlugin(&squarer);

            return manager.processAll(3);  // 3 -> 6 -> 36
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 36)) << "Expected exit code 36";
}

/**
 * E2E Test 13: Event Handler System - DISABLED
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_EventHandlerSystem) {
    std::string cppCode = R"(
        class EventHandler {
        public:
            virtual int handleEvent(int eventType) = 0;
        };

        class ClickHandler : public EventHandler {
        public:
            int handleEvent(int eventType) override {
                return (eventType == 1) ? 10 : 0;
            }
        };

        class KeyHandler : public EventHandler {
        public:
            int handleEvent(int eventType) override {
                return (eventType == 2) ? 20 : 0;
            }
        };

        class EventDispatcher {
        private:
            EventHandler* handlers[10];
            int handlerCount;
        public:
            EventDispatcher() : handlerCount(0) {}
            void addHandler(EventHandler* h) {
                if (handlerCount < 10) handlers[handlerCount++] = h;
            }
            int dispatch(int eventType) {
                int result = 0;
                for (int i = 0; i < handlerCount; i++) {
                    result += handlers[i]->handleEvent(eventType);
                }
                return result;
            }
        };

        int main() {
            EventDispatcher dispatcher;
            ClickHandler clickHandler;
            KeyHandler keyHandler;

            dispatcher.addHandler(&clickHandler);
            dispatcher.addHandler(&keyHandler);

            int clickResult = dispatcher.dispatch(1);  // 10
            int keyResult = dispatcher.dispatch(2);    // 20

            return clickResult + keyResult;  // Returns 30
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 30)) << "Expected exit code 30";
}

/**
 * E2E Test 14: Virtual Destructor Chain - DISABLED
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_VirtualDestructorChain) {
    std::string cppCode = R"(
        int destructorCount = 0;

        class Base {
        public:
            virtual ~Base() {
                destructorCount++;
            }
        };

        class Derived : public Base {
        public:
            ~Derived() override {
                destructorCount++;
            }
        };

        int main() {
            {
                Derived d;
            }
            return destructorCount;  // Should be 2 (both destructors called)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 2)) << "Expected exit code 2";
}

/**
 * E2E Test 15: Diamond Problem Resolution - DISABLED
 *
 * Tests virtual inheritance and diamond problem.
 * This is an advanced scenario requiring VTT (Virtual Table Table).
 */
TEST_F(VirtualMethodsE2ETest, DISABLED_DiamondProblemResolution) {
    std::string cppCode = R"(
        class Base {
        public:
            int value;
            Base() : value(42) {}
            virtual int getValue() {
                return value;
            }
        };

        class Left : public virtual Base {
        public:
            virtual int getLeft() {
                return value * 2;
            }
        };

        class Right : public virtual Base {
        public:
            virtual int getRight() {
                return value * 3;
            }
        };

        class Diamond : public Left, public Right {
        public:
            int getDiamond() {
                return getLeft() + getRight();
            }
        };

        int main() {
            Diamond d;
            return d.getDiamond();  // (42*2) + (42*3) = 84 + 126 = 210
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 210)) << "Expected exit code 210";
}
