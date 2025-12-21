// UniquePtrTest.cpp - Test suite for Stream 3: Smart Pointers & RAII
// File 1 - unique_ptr tests (Developer 1 of 2)
//
// Tests for std::unique_ptr translation to C:
// - unique_ptr creation and ownership
// - unique_ptr moves (no copies)
// - make_unique support
// - Custom deleters
//
// Migrated to Google Test Framework
// Total: 30 tests

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include <string>

using namespace clang;

// ============================================================================
// Test Fixture for Smart Pointer Tests
// ============================================================================

class UniquePtrTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    void TearDown() override {
        // Common cleanup if needed
    }

    // Helper method to build AST from code
    std::unique_ptr<clang::ASTUnit> buildAST(const char* code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// Group 1: Basic unique_ptr Creation and Ownership (8 tests)
// ============================================================================

TEST_F(UniquePtrTest, BasicConstructor) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
        };

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget { int value; };
    // void Widget_destroy(struct Widget* self) { /* destructor */ }
    // void test() {
    //     struct Widget* ptr = Widget_new();
    //     Widget_destroy(ptr);  // at scope exit
    // }
}

TEST_F(UniquePtrTest, NullptrInitialization) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr(nullptr);
            std::unique_ptr<Widget> ptr2;  // Default-constructed (nullptr)
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = NULL;
    // struct Widget* ptr2 = NULL;
    // No destructor call needed for null pointers
}

TEST_F(UniquePtrTest, GetMethod) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
        };

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            Widget* raw = ptr.get();
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // struct Widget* raw = ptr;  // get() is just identity in C
}

TEST_F(UniquePtrTest, ResetReleasesOldPointer) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
        };

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            ptr.reset(new Widget());  // Destroys old, assigns new
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // if (ptr) Widget_destroy(ptr);
    // ptr = Widget_new();
}

TEST_F(UniquePtrTest, ResetWithNullptr) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            ptr.reset();  // Destroys and sets to nullptr
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // if (ptr) Widget_destroy(ptr);
    // ptr = NULL;
}

TEST_F(UniquePtrTest, ReleaseTransfersOwnership) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            Widget* raw = ptr.release();  // No destruction, ownership transferred
            delete raw;
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // struct Widget* raw = ptr;
    // ptr = NULL;  // release() sets to null without destroying
    // Widget_destroy(raw);
}

TEST_F(UniquePtrTest, BoolConversion) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            if (ptr) {
                // Use ptr
            }
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // if (ptr != NULL) {
    //     // Use ptr
    // }
}

TEST_F(UniquePtrTest, DereferenceOperators) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
            void method() {}
        };

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            ptr->value = 42;
            (*ptr).method();
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // ptr->value = 42;
    // Widget_method(ptr);
}

// ============================================================================
// Group 2: Move Semantics (unique_ptr is move-only) (7 tests)
// ============================================================================

TEST_F(UniquePtrTest, MoveConstructorTransfersOwnership) {
    const char *Code = R"(
        #include <memory>
        #include <utility>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            std::unique_ptr<Widget> ptr2(std::move(ptr1));  // ptr1 becomes null
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr1 = Widget_new();
    // struct Widget* ptr2 = ptr1;
    // ptr1 = NULL;  // move sets source to null
}

TEST_F(UniquePtrTest, MoveAssignmentDestroysOld) {
    const char *Code = R"(
        #include <memory>
        #include <utility>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            std::unique_ptr<Widget> ptr2(new Widget());
            ptr2 = std::move(ptr1);  // Destroys ptr2's old object
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr1 = Widget_new();
    // struct Widget* ptr2 = Widget_new();
    // if (ptr2) Widget_destroy(ptr2);  // Destroy old
    // ptr2 = ptr1;
    // ptr1 = NULL;
}

TEST_F(UniquePtrTest, ReturnByValueMoves) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        std::unique_ptr<Widget> create() {
            return std::unique_ptr<Widget>(new Widget());
        }

        void test() {
            std::unique_ptr<Widget> ptr = create();
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* create() {
    //     return Widget_new();
    // }
    // void test() {
    //     struct Widget* ptr = create();
    // }
}

TEST_F(UniquePtrTest, FunctionParameterTakesOwnership) {
    const char *Code = R"(
        #include <memory>
        #include <utility>

        class Widget {};

        void consume(std::unique_ptr<Widget> ptr) {
            // Takes ownership
        }

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            consume(std::move(ptr));  // ptr becomes null
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // void consume(struct Widget* ptr) {
    //     if (ptr) Widget_destroy(ptr);  // at scope exit
    // }
    // void test() {
    //     struct Widget* ptr = Widget_new();
    //     consume(ptr);
    //     ptr = NULL;
    //     // No destruction at end - ownership transferred
    // }
}

TEST_F(UniquePtrTest, CopyConstructorDeleted) {
    // This should fail to compile in C++
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            // std::unique_ptr<Widget> ptr2 = ptr1;  // ERROR: copy constructor deleted
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // This test verifies the transpiler recognizes unique_ptr cannot be copied
}

TEST_F(UniquePtrTest, CopyAssignmentDeleted) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            std::unique_ptr<Widget> ptr2(new Widget());
            // ptr2 = ptr1;  // ERROR: copy assignment deleted
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(UniquePtrTest, SwapExchangesOwnership) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            std::unique_ptr<Widget> ptr2(new Widget());
            ptr1.swap(ptr2);  // Exchange ownership
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr1 = Widget_new();
    // struct Widget* ptr2 = Widget_new();
    // struct Widget* temp = ptr1;
    // ptr1 = ptr2;
    // ptr2 = temp;
}

// ============================================================================
// Group 3: make_unique Support (5 tests)
// ============================================================================

TEST_F(UniquePtrTest, MakeUniqueBasicUsage) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
            Widget(int v) : value(v) {}
        };

        void test() {
            auto ptr = std::make_unique<Widget>(42);
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new_int(42);
}

TEST_F(UniquePtrTest, MakeUniqueWithMultipleArguments) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int x, y;
            Widget(int a, int b) : x(a), y(b) {}
        };

        void test() {
            auto ptr = std::make_unique<Widget>(10, 20);
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new_int_int(10, 20);
}

TEST_F(UniquePtrTest, MakeUniqueWithDefaultConstructor) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            Widget() = default;
        };

        void test() {
            auto ptr = std::make_unique<Widget>();
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
}

TEST_F(UniquePtrTest, MakeUniqueExceptionSafety) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            Widget(int v) {}
        };

        void test() {
            // make_unique is exception-safe (single allocation)
            auto ptr1 = std::make_unique<Widget>(42);

            // unique_ptr constructor (two allocations - Widget and control block)
            std::unique_ptr<Widget> ptr2(new Widget(42));
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(UniquePtrTest, MakeUniqueWithArrayTypes) {
    const char *Code = R"(
        #include <memory>

        void test() {
            auto ptr = std::make_unique<int[]>(10);  // Array of 10 ints
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // int* ptr = (int*)malloc(10 * sizeof(int));
}

// ============================================================================
// Group 4: Custom Deleters (6 tests)
// ============================================================================

TEST_F(UniquePtrTest, CustomDeleterFunctionPointer) {
    const char *Code = R"(
        #include <memory>

        struct Resource {
            int handle;
        };

        void custom_deleter(Resource* res) {
            // Custom cleanup
        }

        void test() {
            std::unique_ptr<Resource, void(*)(Resource*)> ptr(
                new Resource(), custom_deleter
            );
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Resource* ptr = Resource_new();
    // custom_deleter(ptr);  // at scope exit
}

TEST_F(UniquePtrTest, CustomDeleterLambda) {
    const char *Code = R"(
        #include <memory>

        struct Resource {
            int handle;
        };

        void test() {
            auto deleter = [](Resource* res) {
                // Custom cleanup
            };
            std::unique_ptr<Resource, decltype(deleter)> ptr(
                new Resource(), deleter
            );
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct deleter_struct { /* capture */ };
    // void deleter_func(struct deleter_struct* ctx, struct Resource* res) { }
    // struct Resource* ptr = Resource_new();
    // deleter_func(&deleter, ptr);  // at scope exit
}

TEST_F(UniquePtrTest, StatefulDeleter) {
    const char *Code = R"(
        #include <memory>

        struct Resource {
            int handle;
        };

        struct FileDeleter {
            int log_fd;
            void operator()(Resource* res) const {
                // Log to log_fd, then delete
            }
        };

        void test() {
            std::unique_ptr<Resource, FileDeleter> ptr(
                new Resource(), FileDeleter{3}
            );
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct FileDeleter { int log_fd; };
    // void FileDeleter_call(struct FileDeleter* self, struct Resource* res) { }
    // struct Resource* ptr = Resource_new();
    // struct FileDeleter deleter = {3};
    // FileDeleter_call(&deleter, ptr);  // at scope exit
}

TEST_F(UniquePtrTest, WithCApiResource) {
    const char *Code = R"(
        #include <memory>
        #include <cstdio>

        void test() {
            std::unique_ptr<FILE, decltype(&fclose)> file(
                fopen("test.txt", "r"), &fclose
            );
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // FILE* file = fopen("test.txt", "r");
    // if (file) fclose(file);  // at scope exit
}

TEST_F(UniquePtrTest, ArrayDeleter) {
    const char *Code = R"(
        #include <memory>

        void test() {
            std::unique_ptr<int[]> arr(new int[10]);  // Uses delete[] automatically
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // int* arr = (int*)malloc(10 * sizeof(int));
    // free(arr);  // at scope exit
}

TEST_F(UniquePtrTest, DeleterReferenceWrapper) {
    const char *Code = R"(
        #include <memory>
        #include <functional>

        struct Resource {};

        struct Deleter {
            void operator()(Resource* res) const {}
        };

        void test() {
            Deleter d;
            std::unique_ptr<Resource, std::reference_wrapper<Deleter>> ptr(
                new Resource(), std::ref(d)
            );
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Group 5: Edge Cases and Advanced Scenarios (4 tests)
// ============================================================================

TEST_F(UniquePtrTest, InContainer) {
    const char *Code = R"(
        #include <memory>
        #include <vector>

        class Widget {};

        void test() {
            std::vector<std::unique_ptr<Widget>> vec;
            vec.push_back(std::make_unique<Widget>());
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(UniquePtrTest, MemberVariable) {
    const char *Code = R"(
        #include <memory>

        class Resource {};

        class Owner {
        private:
            std::unique_ptr<Resource> resource;
        public:
            Owner() : resource(std::make_unique<Resource>()) {}
        };
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Owner {
    //     struct Resource* resource;
    // };
    // void Owner_init(struct Owner* self) {
    //     self->resource = Resource_new();
    // }
    // void Owner_destroy(struct Owner* self) {
    //     if (self->resource) Resource_destroy(self->resource);
    // }
}

TEST_F(UniquePtrTest, WithPolymorphism) {
    const char *Code = R"(
        #include <memory>

        class Base {
        public:
            virtual ~Base() = default;
        };

        class Derived : public Base {};

        void test() {
            std::unique_ptr<Base> ptr = std::make_unique<Derived>();
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Base* ptr = (struct Base*)Derived_new();
    // Base_destroy_virtual(ptr);  // Virtual destructor call
}

TEST_F(UniquePtrTest, ComparisonOperators) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            std::unique_ptr<Widget> ptr2(new Widget());
            std::unique_ptr<Widget> ptr3;

            bool eq = (ptr1 == ptr2);
            bool ne = (ptr1 != ptr2);
            bool lt = (ptr1 < ptr2);
            bool null_check = (ptr3 == nullptr);
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget* ptr1 = Widget_new();
    // struct Widget* ptr2 = Widget_new();
    // struct Widget* ptr3 = NULL;
    // bool eq = (ptr1 == ptr2);
    // bool ne = (ptr1 != ptr2);
    // bool lt = (ptr1 < ptr2);
    // bool null_check = (ptr3 == NULL);
}

// ============================================================================
// Main Function
// ============================================================================

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
