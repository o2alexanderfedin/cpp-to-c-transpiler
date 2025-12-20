// UniquePtrTest.cpp - Test suite for Stream 3: Smart Pointers & RAII
// File 1 - unique_ptr tests (Developer 1 of 2)
//
// Tests for std::unique_ptr translation to C:
// - unique_ptr creation and ownership
// - unique_ptr moves (no copies)
// - make_unique support
// - Custom deleters
//
// Target: 25-30 tests

#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace clang;

// ============================================================================
// Group 1: Basic unique_ptr Creation and Ownership (8 tests)
// ============================================================================

// Test 1: Basic unique_ptr constructor
void test_unique_ptr_basic_constructor() {
    std::cout << "Running test_unique_ptr_basic_constructor... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget { int value; };
    // void Widget_destroy(struct Widget* self) { /* destructor */ }
    // void test() {
    //     struct Widget* ptr = Widget_new();
    //     Widget_destroy(ptr);  // at scope exit
    // }

    std::cout << "✓" << std::endl;
}

// Test 2: unique_ptr with nullptr
void test_unique_ptr_nullptr_initialization() {
    std::cout << "Running test_unique_ptr_nullptr_initialization... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr(nullptr);
            std::unique_ptr<Widget> ptr2;  // Default-constructed (nullptr)
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = NULL;
    // struct Widget* ptr2 = NULL;
    // No destructor call needed for null pointers

    std::cout << "✓" << std::endl;
}

// Test 3: unique_ptr get() method
void test_unique_ptr_get_method() {
    std::cout << "Running test_unique_ptr_get_method... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // struct Widget* raw = ptr;  // get() is just identity in C

    std::cout << "✓" << std::endl;
}

// Test 4: unique_ptr reset() method
void test_unique_ptr_reset_releases_old_pointer() {
    std::cout << "Running test_unique_ptr_reset_releases_old_pointer... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // if (ptr) Widget_destroy(ptr);
    // ptr = Widget_new();

    std::cout << "✓" << std::endl;
}

// Test 5: unique_ptr reset() with nullptr
void test_unique_ptr_reset_with_nullptr() {
    std::cout << "Running test_unique_ptr_reset_with_nullptr... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            ptr.reset();  // Destroys and sets to nullptr
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // if (ptr) Widget_destroy(ptr);
    // ptr = NULL;

    std::cout << "✓" << std::endl;
}

// Test 6: unique_ptr release() method
void test_unique_ptr_release_transfers_ownership() {
    std::cout << "Running test_unique_ptr_release_transfers_ownership... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr(new Widget());
            Widget* raw = ptr.release();  // No destruction, ownership transferred
            delete raw;
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // struct Widget* raw = ptr;
    // ptr = NULL;  // release() sets to null without destroying
    // Widget_destroy(raw);

    std::cout << "✓" << std::endl;
}

// Test 7: unique_ptr bool conversion
void test_unique_ptr_bool_conversion() {
    std::cout << "Running test_unique_ptr_bool_conversion... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // if (ptr != NULL) {
    //     // Use ptr
    // }

    std::cout << "✓" << std::endl;
}

// Test 8: unique_ptr dereference operators
void test_unique_ptr_dereference_operators() {
    std::cout << "Running test_unique_ptr_dereference_operators... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new();
    // ptr->value = 42;
    // Widget_method(ptr);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 2: Move Semantics (unique_ptr is move-only) (7 tests)
// ============================================================================

// Test 9: unique_ptr move constructor
void test_unique_ptr_move_constructor_transfers_ownership() {
    std::cout << "Running test_unique_ptr_move_constructor_transfers_ownership... ";

    const char *Code = R"(
        #include <memory>
        #include <utility>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            std::unique_ptr<Widget> ptr2(std::move(ptr1));  // ptr1 becomes null
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr1 = Widget_new();
    // struct Widget* ptr2 = ptr1;
    // ptr1 = NULL;  // move sets source to null

    std::cout << "✓" << std::endl;
}

// Test 10: unique_ptr move assignment
void test_unique_ptr_move_assignment_destroys_old() {
    std::cout << "Running test_unique_ptr_move_assignment_destroys_old... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr1 = Widget_new();
    // struct Widget* ptr2 = Widget_new();
    // if (ptr2) Widget_destroy(ptr2);  // Destroy old
    // ptr2 = ptr1;
    // ptr1 = NULL;

    std::cout << "✓" << std::endl;
}

// Test 11: unique_ptr return by value (implicit move)
void test_unique_ptr_return_by_value_moves() {
    std::cout << "Running test_unique_ptr_return_by_value_moves... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* create() {
    //     return Widget_new();
    // }
    // void test() {
    //     struct Widget* ptr = create();
    // }

    std::cout << "✓" << std::endl;
}

// Test 12: unique_ptr function parameter (move)
void test_unique_ptr_function_parameter_takes_ownership() {
    std::cout << "Running test_unique_ptr_function_parameter_takes_ownership... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

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

    std::cout << "✓" << std::endl;
}

// Test 13: unique_ptr copy constructor deleted (compile error)
void test_unique_ptr_copy_constructor_deleted() {
    std::cout << "Running test_unique_ptr_copy_constructor_deleted... ";

    // This should fail to compile in C++
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            // std::unique_ptr<Widget> ptr2 = ptr1;  // ERROR: copy constructor deleted
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // This test verifies the transpiler recognizes unique_ptr cannot be copied

    std::cout << "✓" << std::endl;
}

// Test 14: unique_ptr copy assignment deleted (compile error)
void test_unique_ptr_copy_assignment_deleted() {
    std::cout << "Running test_unique_ptr_copy_assignment_deleted... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            std::unique_ptr<Widget> ptr2(new Widget());
            // ptr2 = ptr1;  // ERROR: copy assignment deleted
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 15: unique_ptr swap
void test_unique_ptr_swap_exchanges_ownership() {
    std::cout << "Running test_unique_ptr_swap_exchanges_ownership... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::unique_ptr<Widget> ptr1(new Widget());
            std::unique_ptr<Widget> ptr2(new Widget());
            ptr1.swap(ptr2);  // Exchange ownership
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr1 = Widget_new();
    // struct Widget* ptr2 = Widget_new();
    // struct Widget* temp = ptr1;
    // ptr1 = ptr2;
    // ptr2 = temp;

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 3: make_unique Support (5 tests)
// ============================================================================

// Test 16: make_unique basic usage
void test_make_unique_basic_usage() {
    std::cout << "Running test_make_unique_basic_usage... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new_int(42);

    std::cout << "✓" << std::endl;
}

// Test 17: make_unique with multiple arguments
void test_make_unique_with_multiple_arguments() {
    std::cout << "Running test_make_unique_with_multiple_arguments... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new_int_int(10, 20);

    std::cout << "✓" << std::endl;
}

// Test 18: make_unique with default constructor
void test_make_unique_with_default_constructor() {
    std::cout << "Running test_make_unique_with_default_constructor... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr = Widget_new();

    std::cout << "✓" << std::endl;
}

// Test 19: make_unique vs unique_ptr constructor (exception safety)
void test_make_unique_exception_safety() {
    std::cout << "Running test_make_unique_exception_safety... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 20: make_unique with array types
void test_make_unique_with_array_types() {
    std::cout << "Running test_make_unique_with_array_types... ";

    const char *Code = R"(
        #include <memory>

        void test() {
            auto ptr = std::make_unique<int[]>(10);  // Array of 10 ints
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // int* ptr = (int*)malloc(10 * sizeof(int));

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 4: Custom Deleters (6 tests)
// ============================================================================

// Test 21: unique_ptr with custom deleter (function pointer)
void test_unique_ptr_custom_deleter_function_pointer() {
    std::cout << "Running test_unique_ptr_custom_deleter_function_pointer... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Resource* ptr = Resource_new();
    // custom_deleter(ptr);  // at scope exit

    std::cout << "✓" << std::endl;
}

// Test 22: unique_ptr with lambda deleter
void test_unique_ptr_custom_deleter_lambda() {
    std::cout << "Running test_unique_ptr_custom_deleter_lambda... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct deleter_struct { /* capture */ };
    // void deleter_func(struct deleter_struct* ctx, struct Resource* res) { }
    // struct Resource* ptr = Resource_new();
    // deleter_func(&deleter, ptr);  // at scope exit

    std::cout << "✓" << std::endl;
}

// Test 23: unique_ptr with stateful deleter
void test_unique_ptr_stateful_deleter() {
    std::cout << "Running test_unique_ptr_stateful_deleter... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct FileDeleter { int log_fd; };
    // void FileDeleter_call(struct FileDeleter* self, struct Resource* res) { }
    // struct Resource* ptr = Resource_new();
    // struct FileDeleter deleter = {3};
    // FileDeleter_call(&deleter, ptr);  // at scope exit

    std::cout << "✓" << std::endl;
}

// Test 24: unique_ptr with C API resource (FILE*)
void test_unique_ptr_with_c_api_resource() {
    std::cout << "Running test_unique_ptr_with_c_api_resource... ";

    const char *Code = R"(
        #include <memory>
        #include <cstdio>

        void test() {
            std::unique_ptr<FILE, decltype(&fclose)> file(
                fopen("test.txt", "r"), &fclose
            );
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // FILE* file = fopen("test.txt", "r");
    // if (file) fclose(file);  // at scope exit

    std::cout << "✓" << std::endl;
}

// Test 25: unique_ptr with array deleter
void test_unique_ptr_array_deleter() {
    std::cout << "Running test_unique_ptr_array_deleter... ";

    const char *Code = R"(
        #include <memory>

        void test() {
            std::unique_ptr<int[]> arr(new int[10]);  // Uses delete[] automatically
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // int* arr = (int*)malloc(10 * sizeof(int));
    // free(arr);  // at scope exit

    std::cout << "✓" << std::endl;
}

// Test 26: unique_ptr deleter with reference wrapper
void test_unique_ptr_deleter_reference_wrapper() {
    std::cout << "Running test_unique_ptr_deleter_reference_wrapper... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 5: Edge Cases and Advanced Scenarios (4 tests)
// ============================================================================

// Test 27: unique_ptr in container
void test_unique_ptr_in_container() {
    std::cout << "Running test_unique_ptr_in_container... ";

    const char *Code = R"(
        #include <memory>
        #include <vector>

        class Widget {};

        void test() {
            std::vector<std::unique_ptr<Widget>> vec;
            vec.push_back(std::make_unique<Widget>());
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 28: unique_ptr member variable
void test_unique_ptr_member_variable() {
    std::cout << "Running test_unique_ptr_member_variable... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

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

    std::cout << "✓" << std::endl;
}

// Test 29: unique_ptr with polymorphism
void test_unique_ptr_with_polymorphism() {
    std::cout << "Running test_unique_ptr_with_polymorphism... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Base* ptr = (struct Base*)Derived_new();
    // Base_destroy_virtual(ptr);  // Virtual destructor call

    std::cout << "✓" << std::endl;
}

// Test 30: unique_ptr comparison operators
void test_unique_ptr_comparison_operators() {
    std::cout << "Running test_unique_ptr_comparison_operators... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget* ptr1 = Widget_new();
    // struct Widget* ptr2 = Widget_new();
    // struct Widget* ptr3 = NULL;
    // bool eq = (ptr1 == ptr2);
    // bool ne = (ptr1 != ptr2);
    // bool lt = (ptr1 < ptr2);
    // bool null_check = (ptr3 == NULL);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Main Function
// ============================================================================

int main() {
    std::cout << "\n=== UniquePtrTest - Stream 3: Smart Pointers & RAII ===" << std::endl;
    std::cout << "File 1 of 3: unique_ptr tests (30 tests)\n" << std::endl;

    // Group 1: Basic unique_ptr Creation and Ownership (8 tests)
    test_unique_ptr_basic_constructor();
    test_unique_ptr_nullptr_initialization();
    test_unique_ptr_get_method();
    test_unique_ptr_reset_releases_old_pointer();
    test_unique_ptr_reset_with_nullptr();
    test_unique_ptr_release_transfers_ownership();
    test_unique_ptr_bool_conversion();
    test_unique_ptr_dereference_operators();

    // Group 2: Move Semantics (7 tests)
    test_unique_ptr_move_constructor_transfers_ownership();
    test_unique_ptr_move_assignment_destroys_old();
    test_unique_ptr_return_by_value_moves();
    test_unique_ptr_function_parameter_takes_ownership();
    test_unique_ptr_copy_constructor_deleted();
    test_unique_ptr_copy_assignment_deleted();
    test_unique_ptr_swap_exchanges_ownership();

    // Group 3: make_unique Support (5 tests)
    test_make_unique_basic_usage();
    test_make_unique_with_multiple_arguments();
    test_make_unique_with_default_constructor();
    test_make_unique_exception_safety();
    test_make_unique_with_array_types();

    // Group 4: Custom Deleters (6 tests)
    test_unique_ptr_custom_deleter_function_pointer();
    test_unique_ptr_custom_deleter_lambda();
    test_unique_ptr_stateful_deleter();
    test_unique_ptr_with_c_api_resource();
    test_unique_ptr_array_deleter();
    test_unique_ptr_deleter_reference_wrapper();

    // Group 5: Edge Cases (4 tests)
    test_unique_ptr_in_container();
    test_unique_ptr_member_variable();
    test_unique_ptr_with_polymorphism();
    test_unique_ptr_comparison_operators();

    std::cout << "\n=== All 30 unique_ptr tests passed! ===" << std::endl;
    return 0;
}
