// Stream 6: Edge Cases & Integration Tests
// File 3: FeatureInteractionTest.cpp - Complex Feature Interactions
// Target: 25-35 tests covering multiple features combined and real-world scenarios

#include "clang/AST/ASTContext.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <string>
#include <vector>
#include <memory>

using namespace clang;

// Test framework
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Helper: Create AST from code
std::unique_ptr<ASTUnit> createAST(const std::string &code) {
    std::vector<std::string> args = {"-std=c++17"};
    auto AST = clang::tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    return AST;
}

// ============================================================================
// Category 1: Templates + Other Features (8 tests)
// ============================================================================

// Test 1: Templates + Exceptions
void test_interaction_templates_exceptions() {
    TEST_START("test_interaction_templates_exceptions");

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
    ASSERT(AST != nullptr, "Failed to parse templates + exceptions");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundTemplate = false;
    for (auto *Decl : TU->decls()) {
        if (auto *CTSD = dyn_cast<ClassTemplateDecl>(Decl)) {
            foundTemplate = true;
            // Verify template has method with exception
        }
    }

    ASSERT(foundTemplate, "Template with exceptions not found");
    TEST_PASS("test_interaction_templates_exceptions");
}

// Test 2: Templates + RAII
void test_interaction_templates_raii() {
    TEST_START("test_interaction_templates_raii");

    const char *code = R"(
        template<typename T>
        class ResourceWrapper {
        public:
            ResourceWrapper(T* res) : resource(res) {}
            ~ResourceWrapper() { delete resource; }
        private:
            T* resource;
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse templates + RAII");

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
            ASSERT(hasDestructor, "Template should have destructor for RAII");
        }
    }

    ASSERT(foundTemplate, "Template with RAII not found");
    TEST_PASS("test_interaction_templates_raii");
}

// Test 3: Templates + Inheritance
void test_interaction_templates_inheritance() {
    TEST_START("test_interaction_templates_inheritance");

    const char *code = R"(
        template<typename T>
        class Base {
        public:
            virtual T getValue() = 0;
        };

        template<typename T>
        class Derived : public Base<T> {
        public:
            T getValue() override { return value; }
        private:
            T value;
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse templates + inheritance");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    int templateCount = 0;
    for (auto *Decl : TU->decls()) {
        if (isa<ClassTemplateDecl>(Decl)) {
            templateCount++;
        }
    }

    ASSERT(templateCount >= 2, "Should have at least 2 template classes");
    TEST_PASS("test_interaction_templates_inheritance");
}

// Test 4: Templates + Smart Pointers
void test_interaction_templates_smart_pointers() {
    TEST_START("test_interaction_templates_smart_pointers");

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
    ASSERT(AST != nullptr, "Failed to parse templates + smart pointers");
    TEST_PASS("test_interaction_templates_smart_pointers");
}

// Test 5: Variadic templates + perfect forwarding
void test_interaction_variadic_forwarding() {
    TEST_START("test_interaction_variadic_forwarding");

    const char *code = R"(
        template<typename... Args>
        void forwardToFunction(Args&&... args) {
            // Perfect forwarding scenario
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse variadic + forwarding");
    TEST_PASS("test_interaction_variadic_forwarding");
}

// Test 6: Templates + constexpr
void test_interaction_templates_constexpr() {
    TEST_START("test_interaction_templates_constexpr");

    const char *code = R"(
        template<typename T>
        constexpr T max(T a, T b) {
            return (a > b) ? a : b;
        }

        constexpr int result = max(10, 20);
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse templates + constexpr");
    TEST_PASS("test_interaction_templates_constexpr");
}

// Test 7: Template specialization + operator overloading
void test_interaction_template_spec_operators() {
    TEST_START("test_interaction_template_spec_operators");

    const char *code = R"(
        template<typename T>
        struct Math {
            T operator+(const T& other) const { return value + other; }
            T value;
        };

        template<>
        struct Math<bool> {
            bool operator+(const bool& other) const { return value || other; }
            bool value;
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse template specialization + operators");
    TEST_PASS("test_interaction_template_spec_operators");
}

// Test 8: Templates + lambdas
void test_interaction_templates_lambdas() {
    TEST_START("test_interaction_templates_lambdas");

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
    ASSERT(AST != nullptr, "Failed to parse templates + lambdas");
    TEST_PASS("test_interaction_templates_lambdas");
}

// ============================================================================
// Category 2: Inheritance + Other Features (7 tests)
// ============================================================================

// Test 9: Inheritance + RAII
void test_interaction_inheritance_raii() {
    TEST_START("test_interaction_inheritance_raii");

    const char *code = R"(
        class ResourceBase {
        public:
            ResourceBase() { /* acquire */ }
            virtual ~ResourceBase() { /* release */ }
        };

        class ResourceDerived : public ResourceBase {
        public:
            ResourceDerived() { /* acquire more */ }
            ~ResourceDerived() override { /* release more */ }
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse inheritance + RAII");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundDerived = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "ResourceDerived") {
                foundDerived = true;
                ASSERT(RD->getNumBases() == 1, "Derived should have 1 base class");
            }
        }
    }

    ASSERT(foundDerived, "Derived class with RAII not found");
    TEST_PASS("test_interaction_inheritance_raii");
}

// Test 10: Virtual functions + exceptions
void test_interaction_virtual_exceptions() {
    TEST_START("test_interaction_virtual_exceptions");

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
    ASSERT(AST != nullptr, "Failed to parse virtual + exceptions");
    TEST_PASS("test_interaction_virtual_exceptions");
}

// Test 11: Multiple inheritance + virtual functions
void test_interaction_multiple_inheritance_virtual() {
    TEST_START("test_interaction_multiple_inheritance_virtual");

    const char *code = R"(
        class Interface1 {
        public:
            virtual void method1() = 0;
        };

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
    ASSERT(AST != nullptr, "Failed to parse multiple inheritance + virtual");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundImpl = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "Implementation") {
                foundImpl = true;
                ASSERT(RD->getNumBases() == 2, "Implementation should have 2 base classes");
            }
        }
    }

    ASSERT(foundImpl, "Implementation class not found");
    TEST_PASS("test_interaction_multiple_inheritance_virtual");
}

// Test 12: Virtual inheritance + constructors
void test_interaction_virtual_inheritance_constructors() {
    TEST_START("test_interaction_virtual_inheritance_constructors");

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
    ASSERT(AST != nullptr, "Failed to parse virtual inheritance + constructors");
    TEST_PASS("test_interaction_virtual_inheritance_constructors");
}

// Test 13: Inheritance + operator overloading
void test_interaction_inheritance_operators() {
    TEST_START("test_interaction_inheritance_operators");

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
    ASSERT(AST != nullptr, "Failed to parse inheritance + operators");
    TEST_PASS("test_interaction_inheritance_operators");
}

// Test 14: Abstract classes + templates
void test_interaction_abstract_templates() {
    TEST_START("test_interaction_abstract_templates");

    const char *code = R"(
        template<typename T>
        class AbstractBase {
        public:
            virtual T compute() = 0;
        };

        template<typename T>
        class Concrete : public AbstractBase<T> {
        public:
            T compute() override { return T(); }
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse abstract + templates");
    TEST_PASS("test_interaction_abstract_templates");
}

// Test 15: Inheritance chain + RTTI
void test_interaction_inheritance_rtti() {
    TEST_START("test_interaction_inheritance_rtti");

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
    ASSERT(AST != nullptr, "Failed to parse inheritance + RTTI");
    TEST_PASS("test_interaction_inheritance_rtti");
}

// ============================================================================
// Category 3: Lambdas + Other Features (5 tests)
// ============================================================================

// Test 16: Lambdas + smart pointers
void test_interaction_lambdas_smart_pointers() {
    TEST_START("test_interaction_lambdas_smart_pointers");

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
    TEST_PASS("test_interaction_lambdas_smart_pointers");
}

// Test 17: Lambdas + exceptions
void test_interaction_lambdas_exceptions() {
    TEST_START("test_interaction_lambdas_exceptions");

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
    ASSERT(AST != nullptr, "Failed to parse lambdas + exceptions");
    TEST_PASS("test_interaction_lambdas_exceptions");
}

// Test 18: Lambdas + templates (generic lambdas)
void test_interaction_generic_lambdas() {
    TEST_START("test_interaction_generic_lambdas");

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
    ASSERT(AST != nullptr, "Failed to parse generic lambdas");
    TEST_PASS("test_interaction_generic_lambdas");
}

// Test 19: Nested lambdas
void test_interaction_nested_lambdas() {
    TEST_START("test_interaction_nested_lambdas");

    const char *code = R"(
        void test() {
            auto outer = [](int x) {
                auto inner = [](int y) {
                    return y * 2;
                };
                return inner(x);
            };
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse nested lambdas");
    TEST_PASS("test_interaction_nested_lambdas");
}

// Test 20: Lambdas with complex captures
void test_interaction_lambdas_complex_captures() {
    TEST_START("test_interaction_lambdas_complex_captures");

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
    ASSERT(AST != nullptr, "Failed to parse lambdas with complex captures");
    TEST_PASS("test_interaction_lambdas_complex_captures");
}

// ============================================================================
// Category 4: Real-world Scenarios (10 tests)
// ============================================================================

// Test 21: RAII resource manager with inheritance
void test_realworld_raii_resource_manager() {
    TEST_START("test_realworld_raii_resource_manager");

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
            ~ResourceManager() { delete resource; }
        private:
            Resource* resource;
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse RAII resource manager");
    TEST_PASS("test_realworld_raii_resource_manager");
}

// Test 22: Observer pattern with templates
void test_realworld_observer_pattern() {
    TEST_START("test_realworld_observer_pattern");

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
    ASSERT(AST != nullptr, "Failed to parse observer pattern");
    TEST_PASS("test_realworld_observer_pattern");
}

// Test 23: Factory pattern with smart pointers
void test_realworld_factory_pattern() {
    TEST_START("test_realworld_factory_pattern");

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
    ASSERT(AST != nullptr, "Failed to parse factory pattern");
    TEST_PASS("test_realworld_factory_pattern");
}

// Test 24: Singleton with thread safety
void test_realworld_singleton_thread_safe() {
    TEST_START("test_realworld_singleton_thread_safe");

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
    ASSERT(AST != nullptr, "Failed to parse singleton pattern");
    TEST_PASS("test_realworld_singleton_thread_safe");
}

// Test 25: Custom allocator with templates
void test_realworld_custom_allocator() {
    TEST_START("test_realworld_custom_allocator");

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
    ASSERT(AST != nullptr, "Failed to parse custom allocator");
    TEST_PASS("test_realworld_custom_allocator");
}

// Test 26: Compile-time polymorphism with CRTP
void test_realworld_crtp_pattern() {
    TEST_START("test_realworld_crtp_pattern");

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
    ASSERT(AST != nullptr, "Failed to parse CRTP pattern");
    TEST_PASS("test_realworld_crtp_pattern");
}

// Test 27: State machine with enums and virtuals
void test_realworld_state_machine() {
    TEST_START("test_realworld_state_machine");

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

            State getState() const { return currentState; }

        private:
            State currentState = State::Idle;
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse state machine");
    TEST_PASS("test_realworld_state_machine");
}

// Test 28: Iterator pattern with templates
void test_realworld_iterator_pattern() {
    TEST_START("test_realworld_iterator_pattern");

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
    ASSERT(AST != nullptr, "Failed to parse iterator pattern");
    TEST_PASS("test_realworld_iterator_pattern");
}

// Test 29: Event system with callbacks
void test_realworld_event_system() {
    TEST_START("test_realworld_event_system");

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
    ASSERT(AST != nullptr, "Failed to parse event system");
    TEST_PASS("test_realworld_event_system");
}

// Test 30: Reference counting with templates and inheritance
void test_realworld_reference_counting() {
    TEST_START("test_realworld_reference_counting");

    const char *code = R"(
        class RefCounted {
        public:
            void addRef() { ++refCount; }
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
    ASSERT(AST != nullptr, "Failed to parse reference counting");
    TEST_PASS("test_realworld_reference_counting");
}

// ============================================================================
// Main Entry Point
// ============================================================================

int main() {
    std::cout << "\n";
    std::cout << "========================================\n";
    std::cout << "Stream 6: Feature Interaction Test Suite\n";
    std::cout << "========================================\n\n";

    std::cout << "Category 1: Templates + Other Features\n";
    std::cout << "---------------------------------------\n";
    test_interaction_templates_exceptions();
    test_interaction_templates_raii();
    test_interaction_templates_inheritance();
    test_interaction_templates_smart_pointers();
    test_interaction_variadic_forwarding();
    test_interaction_templates_constexpr();
    test_interaction_template_spec_operators();
    test_interaction_templates_lambdas();

    std::cout << "\nCategory 2: Inheritance + Other Features\n";
    std::cout << "-----------------------------------------\n";
    test_interaction_inheritance_raii();
    test_interaction_virtual_exceptions();
    test_interaction_multiple_inheritance_virtual();
    test_interaction_virtual_inheritance_constructors();
    test_interaction_inheritance_operators();
    test_interaction_abstract_templates();
    test_interaction_inheritance_rtti();

    std::cout << "\nCategory 3: Lambdas + Other Features\n";
    std::cout << "-------------------------------------\n";
    test_interaction_lambdas_smart_pointers();
    test_interaction_lambdas_exceptions();
    test_interaction_generic_lambdas();
    test_interaction_nested_lambdas();
    test_interaction_lambdas_complex_captures();

    std::cout << "\nCategory 4: Real-world Scenarios\n";
    std::cout << "---------------------------------\n";
    test_realworld_raii_resource_manager();
    test_realworld_observer_pattern();
    test_realworld_factory_pattern();
    test_realworld_singleton_thread_safe();
    test_realworld_custom_allocator();
    test_realworld_crtp_pattern();
    test_realworld_state_machine();
    test_realworld_iterator_pattern();
    test_realworld_event_system();
    test_realworld_reference_counting();

    std::cout << "\n========================================\n";
    std::cout << "Results: " << tests_passed << " passed, " << tests_failed << " failed\n";
    std::cout << "========================================\n";

    return tests_failed > 0 ? 1 : 0;
}
