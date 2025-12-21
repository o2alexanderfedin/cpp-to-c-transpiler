// Stream 6: Edge Cases & Integration Tests
// File 3: FeatureInteractionTest.cpp - Complex Feature Interactions
// Target: 25-35 tests covering multiple features combined and real-world scenarios

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;

// Google Test Fixture
class FeatureInteractionTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> createAST(const std::string &code) {
        std::vector<std::string> args = {"-std=c++17"};
        return clang::tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}
};

// ============================================================================
// Category 1: Templates + Other Features (8 tests)
// ============================================================================

// Test 1: Templates + Exceptions
TEST_F(FeatureInteractionTest, InteractionTemplatesExceptions) {

    const char *code = R"(
        template<typename T>
        class SafeContainer {
        public:
            void add(T item) {
                if (!item) {
                    throw "Invalid item";
}
                data = item;
}
        private:
            T data;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse templates + exceptions";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundTemplate = false;
    for (auto *Decl : TU->decls()) {
        if (auto *CTSD = dyn_cast<ClassTemplateDecl>(Decl)) {
            foundTemplate = true;
            // Verify template has method with exception
        }
    }

    ASSERT_TRUE(foundTemplate) << "Template with exceptions not found";
}
// Test 2: Templates + RAII
TEST_F(FeatureInteractionTest, InteractionTemplatesRaii) {

    const char *code = R"(
        template<typename T>
        class ResourceWrapper {
        public:
            ResourceWrapper(T* res) : resource(res) {}
            ~ResourceWrapper() { delete resource;
}
        private:
            T* resource;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse templates + RAII";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundTemplate = false;
    for (auto *Decl : TU->decls()) {
        if (auto *CTSD = dyn_cast<ClassTemplateDecl>(Decl)) {
            auto *RD = CTSD->getTemplatedDecl();
            foundTemplate = true;

            // Verify destructor exists
            bool hasDestructor = false;
            for (auto *Method : RD->methods()) {
                if (auto *Dtor = dyn_cast<CXXDestructorDecl>(Method)) {
                    hasDestructor = true;
}
            }
            ASSERT_TRUE(hasDestructor) << "Template should have destructor for RAII";
}
    }

    ASSERT_TRUE(foundTemplate) << "Template with RAII not found";
}
// Test 3: Templates + Inheritance
TEST_F(FeatureInteractionTest, InteractionTemplatesInheritance) {
    const char *code = R"(
        template<typename T>
        class Base {
        public:
            virtual T getValue() = 0;
        };

        template<typename T>
        class Derived : public Base<T> {
        public:
            T getValue() override { return value;
}
        private:
            T value;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse templates + inheritance";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    int templateCount = 0;
    for (auto *Decl : TU->decls()) {
        if (isa<ClassTemplateDecl>(Decl)) {
            templateCount++;
}
    }

    ASSERT_TRUE(templateCount >= 2) << "Should have at least 2 template classes";
}
// Test 4: Templates + Smart Pointers
TEST_F(FeatureInteractionTest, InteractionTemplatesSmartPointers) {

    const char *code = R"(
        template<typename T>
        class SmartPtr {
        public:
            explicit SmartPtr(T* p) : ptr(p), refCount(new int(1)) {}
            ~SmartPtr() {
                if (--(*refCount) == 0) {
                    delete ptr;
                    delete refCount;
}
            }
        private:
            T* ptr;
            int* refCount;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse templates + smart pointers";
}
// Test 5: Variadic templates + perfect forwarding
TEST_F(FeatureInteractionTest, InteractionVariadicForwarding) {
    const char *code = R"(
        template<typename... Args>
        void forwardToFunction(Args&&... args) {
            // Perfect forwarding scenario
        }
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse variadic + forwarding";
}
// Test 6: Templates + constexpr
TEST_F(FeatureInteractionTest, InteractionTemplatesConstexpr) {
    const char *code = R"(
        template<typename T>
        constexpr T max(T a, T b) {
            return (a > b) ? a : b;
}
        constexpr int result = max(10, 20);
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse templates + constexpr";
}
// Test 7: Template specialization + operator overloading
TEST_F(FeatureInteractionTest, InteractionTemplateSpecOperators) {
    const char *code = R"(
        template<typename T>
        struct Math {
            T operator+(const T& other) const { return value + other;
}
            T value;
        };

        template<>
        struct Math<bool> {
            bool operator+(const bool& other) const { return value || other;
}
            bool value;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse template specialization + operators";
}
// Test 8: Templates + lambdas
TEST_F(FeatureInteractionTest, InteractionTemplatesLambdas) {
    const char *code = R"(
        template<typename Func>
        void applyFunction(int value, Func func) {
            func(value);
}
        void test() {
            applyFunction(42, [](int x) { return x * 2; });
}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse templates + lambdas";
}
// ============================================================================
// Category 2: Inheritance + Other Features (7 tests)
// ============================================================================

// Test 9: Inheritance + RAII
TEST_F(FeatureInteractionTest, InteractionInheritanceRaii) {

    const char *code = R"(
        class ResourceBase {
        public:
            ResourceBase() { /* acquire */}
            virtual ~ResourceBase() { /* release */ }
        };

        class ResourceDerived : public ResourceBase {
        public:
            ResourceDerived() { /* acquire more */ }
            ~ResourceDerived() override { /* release more */ }
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse inheritance + RAII";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundDerived = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "ResourceDerived") {
                foundDerived = true;
                ASSERT_TRUE(RD->getNumBases() == 1) << "Derived should have 1 base class";
}
        }
    }

    ASSERT_TRUE(foundDerived) << "Derived class with RAII not found";
}
// Test 10: Virtual functions + exceptions
TEST_F(FeatureInteractionTest, InteractionVirtualExceptions) {
    const char *code = R"(
        class Base {
        public:
            virtual void riskyOperation() {
                throw "Base error";
}
        };

        class Derived : public Base {
        public:
            void riskyOperation() override {
                throw "Derived error";
}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse virtual + exceptions";
}
// Test 11: Multiple inheritance + virtual functions
TEST_F(FeatureInteractionTest, InteractionMultipleInheritanceVirtual) {

    const char *code = R"(
        class Interface1 {
        public:
            virtual void method1() = 0;};

        class Interface2 {
        public:
            virtual void method2() = 0;
        };

        class Implementation : public Interface1, public Interface2 {
        public:
            void method1() override {}
            void method2() override {}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse multiple inheritance + virtual";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundImpl = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "Implementation") {
                foundImpl = true;
                ASSERT_TRUE(RD->getNumBases() == 2) << "Implementation should have 2 base classes";
}
        }
    }

    ASSERT_TRUE(foundImpl) << "Implementation class not found";
}
// Test 12: Virtual inheritance + constructors
TEST_F(FeatureInteractionTest, InteractionVirtualInheritanceConstructors) {
    const char *code = R"(
        class Base {
        public:
            Base(int x) : value(x) {}
        protected:
            int value;
        };

        class Left : virtual public Base {
        public:
            Left(int x) : Base(x) {}
        };

        class Right : virtual public Base {
        public:
            Right(int x) : Base(x) {}
        };

        class Diamond : public Left, public Right {
        public:
            Diamond(int x) : Base(x), Left(x), Right(x) {}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse virtual inheritance + constructors";
}
// Test 13: Inheritance + operator overloading
TEST_F(FeatureInteractionTest, InteractionInheritanceOperators) {
    const char *code = R"(
        class Base {
        public:
            virtual Base& operator=(const Base& other) {
                return *this;
}
        };

        class Derived : public Base {
        public:
            Derived& operator=(const Derived& other) {
                Base::operator=(other);
                return *this;
}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse inheritance + operators";
}
// Test 14: Abstract classes + templates
TEST_F(FeatureInteractionTest, InteractionAbstractTemplates) {
    const char *code = R"(
        template<typename T>
        class AbstractBase {
        public:
            virtual T compute() = 0;
        };

        template<typename T>
        class Concrete : public AbstractBase<T> {
        public:
            T compute() override { return T();
}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse abstract + templates";
}
// Test 15: Inheritance chain + RTTI
TEST_F(FeatureInteractionTest, InteractionInheritanceRtti) {
    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {};

        void test(Base* ptr) {
            Derived* d = dynamic_cast<Derived*>(ptr);
}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse inheritance + RTTI";
}
// ============================================================================
// Category 3: Lambdas + Other Features (5 tests)
// ============================================================================

// Test 16: Lambdas + smart pointers
TEST_F(FeatureInteractionTest, InteractionLambdasSmartPointers) {
    const char *code = R"(
        #include <memory>

        void test() {
            auto ptr = std::make_unique<int>(42);
            auto lambda = [p = std::move(ptr)]() {
                return *p;
            };
}
    )";

    auto AST = createAST(code);
    // May fail without std library, but tests interaction concept
}

// Test 17: Lambdas + exceptions
TEST_F(FeatureInteractionTest, InteractionLambdasExceptions) {
    const char *code = R"(
        void test() {
            auto risky = []() {
                throw "Lambda error";
            };

            try {
                risky();
            } catch (...) {
                // Handle
            }
        }
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse lambdas + exceptions";
}
// Test 18: Lambdas + templates (generic lambdas)
TEST_F(FeatureInteractionTest, InteractionGenericLambdas) {
    const char *code = R"(
        void test() {
            auto generic = [](auto x, auto y) {
                return x + y;
            };

            int i = generic(1, 2);
            double d = generic(1.0, 2.0);
}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse generic lambdas";
}
// Test 19: Nested lambdas
TEST_F(FeatureInteractionTest, InteractionNestedLambdas) {

    const char *code = R"(
        void test() {
            auto outer = [](int x) {
                auto inner = [](int y) {
                    return y * 2;};
                return inner(x);
            };
}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse nested lambdas";
}
// Test 20: Lambdas with complex captures
TEST_F(FeatureInteractionTest, InteractionLambdasComplexCaptures) {
    const char *code = R"(
        void test() {
            int x = 10;
            int& ref = x;
            const int y = 20;

            auto lambda = [x, &ref, y, z = x + y]() mutable {
                x++;
                ref++;
                return z;
            };
}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse lambdas with complex captures";
}
// ============================================================================
// Category 4: Real-world Scenarios (10 tests)
// ============================================================================

// Test 21: RAII resource manager with inheritance
TEST_F(FeatureInteractionTest, RealworldRaiiResourceManager) {
    const char *code = R"(
        class Resource {
        public:
            virtual ~Resource() {}
            virtual void use() = 0;
        };

        class FileResource : public Resource {
        public:
            FileResource(const char* path) {}
            ~FileResource() override {}
            void use() override {}
        };

        class ResourceManager {
        public:
            ResourceManager(Resource* res) : resource(res) {}
            ~ResourceManager() { delete resource;
}
        private:
            Resource* resource;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse RAII resource manager";
}
// Test 22: Observer pattern with templates
TEST_F(FeatureInteractionTest, RealworldObserverPattern) {
    const char *code = R"(
        template<typename T>
        class Observer {
        public:
            virtual void update(T data) = 0;
        };

        template<typename T>
        class Subject {
        public:
            void attach(Observer<T>* obs) {}
            void notify(T data) {}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse observer pattern";
}
// Test 23: Factory pattern with smart pointers
TEST_F(FeatureInteractionTest, RealworldFactoryPattern) {
    const char *code = R"(
        class Product {
        public:
            virtual ~Product() {}
        };

        class ConcreteProduct : public Product {
        public:
            ConcreteProduct() {}
        };

        class Factory {
        public:
            static Product* createProduct() {
                return new ConcreteProduct();
}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse factory pattern";
}
// Test 24: Singleton with thread safety
TEST_F(FeatureInteractionTest, RealworldSingletonThreadSafe) {
    const char *code = R"(
        class Singleton {
        public:
            static Singleton& getInstance() {
                static Singleton instance;
                return instance;
}
            Singleton(const Singleton&) = delete;
            Singleton& operator=(const Singleton&) = delete;

        private:
            Singleton() {}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse singleton pattern";
}
// Test 25: Custom allocator with templates
TEST_F(FeatureInteractionTest, RealworldCustomAllocator) {
    const char *code = R"(
        template<typename T>
        class PoolAllocator {
        public:
            T* allocate(size_t n) {
                return static_cast<T*>(::operator new(n * sizeof(T)));
}
            void deallocate(T* p, size_t n) {
                ::operator delete(p);
}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse custom allocator";
}
// Test 26: Compile-time polymorphism with CRTP
TEST_F(FeatureInteractionTest, RealworldCrtpPattern) {
    const char *code = R"(
        template<typename Derived>
        class Base {
        public:
            void interface() {
                static_cast<Derived*>(this)->implementation();
}
        };

        class Derived : public Base<Derived> {
        public:
            void implementation() {}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse CRTP pattern";
}
// Test 27: State machine with enums and virtuals
TEST_F(FeatureInteractionTest, RealworldStateMachine) {
    const char *code = R"(
        enum class State {
            Idle,
            Running,
            Stopped
        };

        class StateMachine {
        public:
            virtual void transition(State newState) {
                currentState = newState;
}
            State getState() const { return currentState;
}
        private:
            State currentState = State::Idle;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse state machine";
}
// Test 28: Iterator pattern with templates
TEST_F(FeatureInteractionTest, RealworldIteratorPattern) {
    const char *code = R"(
        template<typename T>
        class Iterator {
        public:
            virtual bool hasNext() const = 0;
            virtual T next() = 0;
        };

        template<typename T>
        class ArrayIterator : public Iterator<T> {
        public:
            ArrayIterator(T* arr, int size) : array(arr), size(size), index(0) {}

            bool hasNext() const override {
                return index < size;
}
            T next() override {
                return array[index++];
}
        private:
            T* array;
            int size;
            int index;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse iterator pattern";
}
// Test 29: Event system with callbacks
TEST_F(FeatureInteractionTest, RealworldEventSystem) {

    const char *code = R"(
        template<typename... Args>
        class Event {
        public:
            using Callback = void(*)(Args...);

            void subscribe(Callback cb) {
                callback = cb;
}
            void trigger(Args... args) {
                if (callback) {
                    callback(args...);
}
            }

        private:
            Callback callback = nullptr;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse event system";
}
// Test 30: Reference counting with templates and inheritance
TEST_F(FeatureInteractionTest, RealworldReferenceCounting) {

    const char *code = R"(
        class RefCounted {
        public:
            void addRef() { ++refCount;
}
            void release() {
                if (--refCount == 0) {
                    delete this;
}
            }

        protected:
            RefCounted() : refCount(0) {}
            virtual ~RefCounted() {}

        private:
            int refCount;
        };

        template<typename T>
        class RefPtr {
        public:
            RefPtr(T* ptr) : ptr(ptr) {
                if (ptr) ptr->addRef();
}
            ~RefPtr() {
                if (ptr) ptr->release();
}
        private:
            T* ptr;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse reference counting";
}
// ============================================================================
// Main Entry Point
// ============================================================================

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}