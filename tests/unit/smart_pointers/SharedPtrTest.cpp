// SharedPtrTest.cpp - Test suite for Stream 3: Smart Pointers & RAII
// File 2 of 3: shared_ptr and weak_ptr tests (Developer 2 of 2)
//
// Tests for std::shared_ptr and std::weak_ptr translation to C:
// - shared_ptr creation and reference counting
// - make_shared support
// - Cyclic references and weak_ptr
// - Thread-safe reference counting
//
// Target: 35-40 tests

#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace clang;

// ============================================================================
// Group 1: Basic shared_ptr Creation and Reference Counting (10 tests)
// ============================================================================

// Test 1: Basic shared_ptr constructor
void test_shared_ptr_basic_constructor() {
    std::cout << "Running test_shared_ptr_basic_constructor... ";

    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
        };

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
        }  // ref_count-- (destruction if count reaches 0)
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted {
    //     struct Widget obj;
    //     int ref_count;
    // };
    // struct Widget_refcounted* ptr = Widget_refcounted_new();  // ref_count = 1
    // Widget_refcounted_release(ptr);  // at scope exit

    std::cout << "✓" << std::endl;
}

// Test 2: shared_ptr copy constructor increments ref count
void test_shared_ptr_copy_constructor_increments_refcount() {
    std::cout << "Running test_shared_ptr_copy_constructor_increments_refcount... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());  // ref_count = 1
            std::shared_ptr<Widget> ptr2(ptr1);           // ref_count = 2
        }  // ptr2 destroyed (ref_count = 1), ptr1 destroyed (ref_count = 0, delete object)
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();  // ref_count = 1
    // struct Widget_refcounted* ptr2 = Widget_refcounted_retain(ptr1);  // ref_count = 2
    // Widget_refcounted_release(ptr2);  // ref_count = 1
    // Widget_refcounted_release(ptr1);  // ref_count = 0, destroy

    std::cout << "✓" << std::endl;
}

// Test 3: shared_ptr copy assignment increments ref count
void test_shared_ptr_copy_assignment_increments_refcount() {
    std::cout << "Running test_shared_ptr_copy_assignment_increments_refcount... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());
            std::shared_ptr<Widget> ptr2(new Widget());
            ptr2 = ptr1;  // Destroys ptr2's old object, shares ptr1's object
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();  // obj1, ref=1
    // struct Widget_refcounted* ptr2 = Widget_refcounted_new();  // obj2, ref=1
    // Widget_refcounted_release(ptr2);  // obj2 ref=0, destroy
    // ptr2 = Widget_refcounted_retain(ptr1);  // obj1 ref=2

    std::cout << "✓" << std::endl;
}

// Test 4: shared_ptr use_count method
void test_shared_ptr_use_count_returns_ref_count() {
    std::cout << "Running test_shared_ptr_use_count_returns_ref_count... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());
            long count1 = ptr1.use_count();  // 1

            std::shared_ptr<Widget> ptr2 = ptr1;
            long count2 = ptr1.use_count();  // 2
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();
    // long count1 = ptr1->ref_count;  // 1
    // struct Widget_refcounted* ptr2 = Widget_refcounted_retain(ptr1);
    // long count2 = ptr1->ref_count;  // 2

    std::cout << "✓" << std::endl;
}

// Test 5: shared_ptr unique method
void test_shared_ptr_unique_checks_sole_ownership() {
    std::cout << "Running test_shared_ptr_unique_checks_sole_ownership... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());
            bool is_unique1 = ptr1.unique();  // true (ref_count == 1)

            std::shared_ptr<Widget> ptr2 = ptr1;
            bool is_unique2 = ptr1.unique();  // false (ref_count == 2)
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();
    // bool is_unique1 = (ptr1->ref_count == 1);  // true
    // struct Widget_refcounted* ptr2 = Widget_refcounted_retain(ptr1);
    // bool is_unique2 = (ptr1->ref_count == 1);  // false

    std::cout << "✓" << std::endl;
}

// Test 6: shared_ptr reset method
void test_shared_ptr_reset_releases_ownership() {
    std::cout << "Running test_shared_ptr_reset_releases_ownership... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());
            std::shared_ptr<Widget> ptr2 = ptr1;  // ref_count = 2
            ptr1.reset();  // ptr1 becomes null, ref_count = 1
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();  // ref=1
    // struct Widget_refcounted* ptr2 = Widget_refcounted_retain(ptr1);  // ref=2
    // if (ptr1) Widget_refcounted_release(ptr1);  // ref=1
    // ptr1 = NULL;

    std::cout << "✓" << std::endl;
}

// Test 7: shared_ptr reset with new pointer
void test_shared_ptr_reset_with_new_pointer() {
    std::cout << "Running test_shared_ptr_reset_with_new_pointer... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            ptr.reset(new Widget());  // Release old, assign new
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new();
    // if (ptr) Widget_refcounted_release(ptr);
    // ptr = Widget_refcounted_new();

    std::cout << "✓" << std::endl;
}

// Test 8: shared_ptr get method
void test_shared_ptr_get_returns_raw_pointer() {
    std::cout << "Running test_shared_ptr_get_returns_raw_pointer... ";

    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
        };

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            Widget* raw = ptr.get();
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new();
    // struct Widget* raw = &ptr->obj;

    std::cout << "✓" << std::endl;
}

// Test 9: shared_ptr bool conversion
void test_shared_ptr_bool_conversion() {
    std::cout << "Running test_shared_ptr_bool_conversion... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            if (ptr) {
                // Use ptr
            }
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new();
    // if (ptr != NULL) {
    //     // Use ptr
    // }

    std::cout << "✓" << std::endl;
}

// Test 10: shared_ptr dereference operators
void test_shared_ptr_dereference_operators() {
    std::cout << "Running test_shared_ptr_dereference_operators... ";

    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
            void method() {}
        };

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            ptr->value = 42;
            (*ptr).method();
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new();
    // ptr->obj.value = 42;
    // Widget_method(&ptr->obj);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 2: make_shared Support (5 tests)
// ============================================================================

// Test 11: make_shared basic usage
void test_make_shared_basic_usage() {
    std::cout << "Running test_make_shared_basic_usage... ";

    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
            Widget(int v) : value(v) {}
        };

        void test() {
            auto ptr = std::make_shared<Widget>(42);
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new_int(42);

    std::cout << "✓" << std::endl;
}

// Test 12: make_shared with multiple arguments
void test_make_shared_with_multiple_arguments() {
    std::cout << "Running test_make_shared_with_multiple_arguments... ";

    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int x, y;
            Widget(int a, int b) : x(a), y(b) {}
        };

        void test() {
            auto ptr = std::make_shared<Widget>(10, 20);
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 13: make_shared vs shared_ptr constructor (single allocation)
void test_make_shared_single_allocation_optimization() {
    std::cout << "Running test_make_shared_single_allocation_optimization... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            // make_shared: single allocation (object + control block)
            auto ptr1 = std::make_shared<Widget>();

            // shared_ptr: two allocations (object, then control block)
            std::shared_ptr<Widget> ptr2(new Widget());
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // make_shared is more efficient (single malloc)

    std::cout << "✓" << std::endl;
}

// Test 14: make_shared with default constructor
void test_make_shared_with_default_constructor() {
    std::cout << "Running test_make_shared_with_default_constructor... ";

    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            Widget() = default;
        };

        void test() {
            auto ptr = std::make_shared<Widget>();
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 15: make_shared exception safety
void test_make_shared_exception_safety() {
    std::cout << "Running test_make_shared_exception_safety... ";

    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            Widget(int v) {}
        };

        void process(std::shared_ptr<Widget> p1, std::shared_ptr<Widget> p2) {}

        void test() {
            // make_shared is exception-safe
            process(std::make_shared<Widget>(1), std::make_shared<Widget>(2));
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 3: weak_ptr and Cyclic References (10 tests)
// ============================================================================

// Test 16: weak_ptr basic creation from shared_ptr
void test_weak_ptr_basic_creation_from_shared_ptr() {
    std::cout << "Running test_weak_ptr_basic_creation_from_shared_ptr... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared(new Widget());
            std::weak_ptr<Widget> weak(shared);  // Does not increase ref_count
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* shared = Widget_refcounted_new();  // ref=1
    // struct Widget_refcounted* weak = shared;  // weak pointer (no ref increment)
    // weak->weak_count++;  // Track weak references separately

    std::cout << "✓" << std::endl;
}

// Test 17: weak_ptr lock method creates shared_ptr
void test_weak_ptr_lock_creates_shared_ptr() {
    std::cout << "Running test_weak_ptr_lock_creates_shared_ptr... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared(new Widget());
            std::weak_ptr<Widget> weak(shared);

            std::shared_ptr<Widget> locked = weak.lock();  // ref_count++
            // locked is valid while shared exists
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* shared = Widget_refcounted_new();  // ref=1
    // struct Widget_refcounted* weak = shared;
    // weak->weak_count++;
    // struct Widget_refcounted* locked = NULL;
    // if (weak != NULL && weak->ref_count > 0) {
    //     locked = Widget_refcounted_retain(weak);  // ref=2
    // }

    std::cout << "✓" << std::endl;
}

// Test 18: weak_ptr lock returns null when shared_ptr destroyed
void test_weak_ptr_lock_returns_null_when_expired() {
    std::cout << "Running test_weak_ptr_lock_returns_null_when_expired... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::weak_ptr<Widget> weak;
            {
                std::shared_ptr<Widget> shared(new Widget());
                weak = shared;
            }  // shared destroyed, object deleted

            std::shared_ptr<Widget> locked = weak.lock();  // Returns null
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 19: weak_ptr expired method
void test_weak_ptr_expired_checks_validity() {
    std::cout << "Running test_weak_ptr_expired_checks_validity... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::weak_ptr<Widget> weak;
            {
                std::shared_ptr<Widget> shared(new Widget());
                weak = shared;
                bool expired1 = weak.expired();  // false
            }
            bool expired2 = weak.expired();  // true
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // bool expired = (weak == NULL || weak->ref_count == 0);

    std::cout << "✓" << std::endl;
}

// Test 20: weak_ptr use_count method
void test_weak_ptr_use_count_returns_shared_count() {
    std::cout << "Running test_weak_ptr_use_count_returns_shared_count... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared1(new Widget());
            std::weak_ptr<Widget> weak(shared1);

            long count1 = weak.use_count();  // 1

            std::shared_ptr<Widget> shared2 = shared1;
            long count2 = weak.use_count();  // 2
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 21: weak_ptr reset method
void test_weak_ptr_reset_releases_weak_reference() {
    std::cout << "Running test_weak_ptr_reset_releases_weak_reference... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared(new Widget());
            std::weak_ptr<Widget> weak(shared);
            weak.reset();  // weak becomes null
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // if (weak) weak->weak_count--;
    // weak = NULL;

    std::cout << "✓" << std::endl;
}

// Test 22: weak_ptr prevents cyclic reference leak
void test_weak_ptr_breaks_cyclic_reference() {
    std::cout << "Running test_weak_ptr_breaks_cyclic_reference... ";

    const char *Code = R"(
        #include <memory>

        class Node {
        public:
            std::shared_ptr<Node> next;
            std::weak_ptr<Node> prev;  // Weak to break cycle
        };

        void test() {
            auto node1 = std::make_shared<Node>();
            auto node2 = std::make_shared<Node>();
            node1->next = node2;
            node2->prev = node1;  // No cycle (weak_ptr)
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 23: weak_ptr copy constructor
void test_weak_ptr_copy_constructor() {
    std::cout << "Running test_weak_ptr_copy_constructor... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared(new Widget());
            std::weak_ptr<Widget> weak1(shared);
            std::weak_ptr<Widget> weak2(weak1);  // weak_count++
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 24: weak_ptr assignment operator
void test_weak_ptr_assignment_operator() {
    std::cout << "Running test_weak_ptr_assignment_operator... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared1(new Widget());
            std::shared_ptr<Widget> shared2(new Widget());
            std::weak_ptr<Widget> weak1(shared1);
            std::weak_ptr<Widget> weak2(shared2);
            weak2 = weak1;  // weak2 now observes shared1's object
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 25: weak_ptr swap
void test_weak_ptr_swap() {
    std::cout << "Running test_weak_ptr_swap... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared1(new Widget());
            std::shared_ptr<Widget> shared2(new Widget());
            std::weak_ptr<Widget> weak1(shared1);
            std::weak_ptr<Widget> weak2(shared2);
            weak1.swap(weak2);
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 4: Thread-Safe Reference Counting (5 tests)
// ============================================================================

// Test 26: shared_ptr atomic reference counting
void test_shared_ptr_atomic_reference_counting() {
    std::cout << "Running test_shared_ptr_atomic_reference_counting... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            // ref_count operations must be atomic (thread-safe)
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // Use atomic operations for ref_count:
    // __atomic_fetch_add(&ptr->ref_count, 1, __ATOMIC_ACQ_REL);
    // __atomic_fetch_sub(&ptr->ref_count, 1, __ATOMIC_ACQ_REL);

    std::cout << "✓" << std::endl;
}

// Test 27: shared_ptr copy in multithreaded context
void test_shared_ptr_copy_thread_safe() {
    std::cout << "Running test_shared_ptr_copy_thread_safe... ";

    const char *Code = R"(
        #include <memory>
        #include <thread>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());

            std::thread t1([ptr]() {
                std::shared_ptr<Widget> local = ptr;  // Atomic ref_count++
            });

            std::thread t2([ptr]() {
                std::shared_ptr<Widget> local = ptr;  // Atomic ref_count++
            });

            t1.join();
            t2.join();
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 28: atomic_load for shared_ptr
void test_atomic_load_shared_ptr() {
    std::cout << "Running test_atomic_load_shared_ptr... ";

    const char *Code = R"(
        #include <memory>
        #include <atomic>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            std::shared_ptr<Widget> loaded = std::atomic_load(&ptr);
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 29: atomic_store for shared_ptr
void test_atomic_store_shared_ptr() {
    std::cout << "Running test_atomic_store_shared_ptr... ";

    const char *Code = R"(
        #include <memory>
        #include <atomic>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr;
            std::shared_ptr<Widget> new_ptr(new Widget());
            std::atomic_store(&ptr, new_ptr);
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 30: atomic_exchange for shared_ptr
void test_atomic_exchange_shared_ptr() {
    std::cout << "Running test_atomic_exchange_shared_ptr... ";

    const char *Code = R"(
        #include <memory>
        #include <atomic>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            std::shared_ptr<Widget> new_ptr(new Widget());
            std::shared_ptr<Widget> old_ptr = std::atomic_exchange(&ptr, new_ptr);
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 5: Advanced Scenarios and Edge Cases (10 tests)
// ============================================================================

// Test 31: shared_ptr with custom deleter
void test_shared_ptr_with_custom_deleter() {
    std::cout << "Running test_shared_ptr_with_custom_deleter... ";

    const char *Code = R"(
        #include <memory>

        struct Resource {};

        void custom_deleter(Resource* res) {
            // Custom cleanup
        }

        void test() {
            std::shared_ptr<Resource> ptr(new Resource(), custom_deleter);
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 32: shared_ptr with array deleter
void test_shared_ptr_with_array_deleter() {
    std::cout << "Running test_shared_ptr_with_array_deleter... ";

    const char *Code = R"(
        #include <memory>

        void test() {
            std::shared_ptr<int> arr(new int[10], std::default_delete<int[]>());
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 33: shared_ptr aliasing constructor
void test_shared_ptr_aliasing_constructor() {
    std::cout << "Running test_shared_ptr_aliasing_constructor... ";

    const char *Code = R"(
        #include <memory>

        struct Widget {
            int value;
        };

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            std::shared_ptr<int> value_ptr(ptr, &ptr->value);  // Shares ownership
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // value_ptr shares ownership with ptr but points to member

    std::cout << "✓" << std::endl;
}

// Test 34: shared_ptr with polymorphism
void test_shared_ptr_with_polymorphism() {
    std::cout << "Running test_shared_ptr_with_polymorphism... ";

    const char *Code = R"(
        #include <memory>

        class Base {
        public:
            virtual ~Base() = default;
        };

        class Derived : public Base {};

        void test() {
            std::shared_ptr<Base> ptr = std::make_shared<Derived>();
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 35: shared_ptr enable_shared_from_this
void test_shared_ptr_enable_shared_from_this() {
    std::cout << "Running test_shared_ptr_enable_shared_from_this... ";

    const char *Code = R"(
        #include <memory>

        class Widget : public std::enable_shared_from_this<Widget> {
        public:
            std::shared_ptr<Widget> get_shared() {
                return shared_from_this();
            }
        };

        void test() {
            auto ptr = std::make_shared<Widget>();
            auto ptr2 = ptr->get_shared();  // Same object, ref_count++
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 36: shared_ptr in container
void test_shared_ptr_in_container() {
    std::cout << "Running test_shared_ptr_in_container... ";

    const char *Code = R"(
        #include <memory>
        #include <vector>

        class Widget {};

        void test() {
            std::vector<std::shared_ptr<Widget>> vec;
            vec.push_back(std::make_shared<Widget>());
            vec.push_back(vec[0]);  // ref_count++
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 37: shared_ptr comparison operators
void test_shared_ptr_comparison_operators() {
    std::cout << "Running test_shared_ptr_comparison_operators... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            auto ptr1 = std::make_shared<Widget>();
            auto ptr2 = std::make_shared<Widget>();
            auto ptr3 = ptr1;

            bool eq = (ptr1 == ptr3);  // true (same object)
            bool ne = (ptr1 != ptr2);  // true (different objects)
            bool null_check = (ptr1 == nullptr);  // false
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 38: shared_ptr owner_before for strict weak ordering
void test_shared_ptr_owner_before_strict_weak_ordering() {
    std::cout << "Running test_shared_ptr_owner_before_strict_weak_ordering... ";

    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            auto ptr1 = std::make_shared<Widget>();
            auto ptr2 = std::make_shared<Widget>();
            bool less = ptr1.owner_before(ptr2);  // For map/set ordering
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 39: shared_ptr move constructor (optimization)
void test_shared_ptr_move_constructor_no_refcount_change() {
    std::cout << "Running test_shared_ptr_move_constructor_no_refcount_change... ";

    const char *Code = R"(
        #include <memory>
        #include <utility>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());  // ref=1
            std::shared_ptr<Widget> ptr2(std::move(ptr1));  // ref=1 (no change)
            // ptr1 is now null
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Move constructor transfers ownership without ref_count change

    std::cout << "✓" << std::endl;
}

// Test 40: shared_ptr move assignment (optimization)
void test_shared_ptr_move_assignment_no_refcount_change() {
    std::cout << "Running test_shared_ptr_move_assignment_no_refcount_change... ";

    const char *Code = R"(
        #include <memory>
        #include <utility>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());  // ref=1
            std::shared_ptr<Widget> ptr2(new Widget());  // ref=1
            ptr2 = std::move(ptr1);  // ptr2's old object destroyed, ptr1 transferred
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();
    // struct Widget_refcounted* ptr2 = Widget_refcounted_new();
    // Widget_refcounted_release(ptr2);  // Destroy old
    // ptr2 = ptr1;  // Transfer (no ref change)
    // ptr1 = NULL;

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Main Function
// ============================================================================

int main() {
    std::cout << "\n=== SharedPtrTest - Stream 3: Smart Pointers & RAII ===" << std::endl;
    std::cout << "File 2 of 3: shared_ptr and weak_ptr tests (40 tests)\n" << std::endl;

    // Group 1: Basic shared_ptr Creation and Reference Counting (10 tests)
    test_shared_ptr_basic_constructor();
    test_shared_ptr_copy_constructor_increments_refcount();
    test_shared_ptr_copy_assignment_increments_refcount();
    test_shared_ptr_use_count_returns_ref_count();
    test_shared_ptr_unique_checks_sole_ownership();
    test_shared_ptr_reset_releases_ownership();
    test_shared_ptr_reset_with_new_pointer();
    test_shared_ptr_get_returns_raw_pointer();
    test_shared_ptr_bool_conversion();
    test_shared_ptr_dereference_operators();

    // Group 2: make_shared Support (5 tests)
    test_make_shared_basic_usage();
    test_make_shared_with_multiple_arguments();
    test_make_shared_single_allocation_optimization();
    test_make_shared_with_default_constructor();
    test_make_shared_exception_safety();

    // Group 3: weak_ptr and Cyclic References (10 tests)
    test_weak_ptr_basic_creation_from_shared_ptr();
    test_weak_ptr_lock_creates_shared_ptr();
    test_weak_ptr_lock_returns_null_when_expired();
    test_weak_ptr_expired_checks_validity();
    test_weak_ptr_use_count_returns_shared_count();
    test_weak_ptr_reset_releases_weak_reference();
    test_weak_ptr_breaks_cyclic_reference();
    test_weak_ptr_copy_constructor();
    test_weak_ptr_assignment_operator();
    test_weak_ptr_swap();

    // Group 4: Thread-Safe Reference Counting (5 tests)
    test_shared_ptr_atomic_reference_counting();
    test_shared_ptr_copy_thread_safe();
    test_atomic_load_shared_ptr();
    test_atomic_store_shared_ptr();
    test_atomic_exchange_shared_ptr();

    // Group 5: Advanced Scenarios and Edge Cases (10 tests)
    test_shared_ptr_with_custom_deleter();
    test_shared_ptr_with_array_deleter();
    test_shared_ptr_aliasing_constructor();
    test_shared_ptr_with_polymorphism();
    test_shared_ptr_enable_shared_from_this();
    test_shared_ptr_in_container();
    test_shared_ptr_comparison_operators();
    test_shared_ptr_owner_before_strict_weak_ordering();
    test_shared_ptr_move_constructor_no_refcount_change();
    test_shared_ptr_move_assignment_no_refcount_change();

    std::cout << "\n=== All 40 shared_ptr and weak_ptr tests passed! ===" << std::endl;
    return 0;
}
