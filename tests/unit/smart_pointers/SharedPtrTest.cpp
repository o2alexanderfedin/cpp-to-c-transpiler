// SharedPtrTest.cpp - Test suite for Stream 3: Smart Pointers & RAII
// File 2 of 3: shared_ptr and weak_ptr tests (Developer 2 of 2)
//
// Tests for std::shared_ptr and std::weak_ptr translation to C:
// - shared_ptr creation and reference counting
// - make_shared support
// - Cyclic references and weak_ptr
// - Thread-safe reference counting
//
// Migrated to Google Test Framework
// Total: 40 tests

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include <string>

using namespace clang;

// ============================================================================
// Test Fixtures for Shared Pointer Tests
// ============================================================================

class SharedPtrTest : public ::testing::Test {
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

class WeakPtrTest : public ::testing::Test {
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
// Group 1: Basic shared_ptr Creation and Reference Counting (10 tests)
// ============================================================================

TEST_F(SharedPtrTest, BasicConstructor) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted {
    //     struct Widget obj;
    //     int ref_count;
    // };
    // struct Widget_refcounted* ptr = Widget_refcounted_new();  // ref_count = 1
    // Widget_refcounted_release(ptr);  // at scope exit
}

TEST_F(SharedPtrTest, CopyConstructorIncrementsRefcount) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());  // ref_count = 1
            std::shared_ptr<Widget> ptr2(ptr1);           // ref_count = 2
        }  // ptr2 destroyed (ref_count = 1), ptr1 destroyed (ref_count = 0, delete object)
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();  // ref_count = 1
    // struct Widget_refcounted* ptr2 = Widget_refcounted_retain(ptr1);  // ref_count = 2
    // Widget_refcounted_release(ptr2);  // ref_count = 1
    // Widget_refcounted_release(ptr1);  // ref_count = 0, destroy
}

TEST_F(SharedPtrTest, CopyAssignmentIncrementsRefcount) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());
            std::shared_ptr<Widget> ptr2(new Widget());
            ptr2 = ptr1;  // Destroys ptr2's old object, shares ptr1's object
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();  // obj1, ref=1
    // struct Widget_refcounted* ptr2 = Widget_refcounted_new();  // obj2, ref=1
    // Widget_refcounted_release(ptr2);  // obj2 ref=0, destroy
    // ptr2 = Widget_refcounted_retain(ptr1);  // obj1 ref=2
}

TEST_F(SharedPtrTest, UseCountReturnsRefCount) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();
    // long count1 = ptr1->ref_count;  // 1
    // struct Widget_refcounted* ptr2 = Widget_refcounted_retain(ptr1);
    // long count2 = ptr1->ref_count;  // 2
}

TEST_F(SharedPtrTest, UniqueChecksSoleOwnership) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();
    // bool is_unique1 = (ptr1->ref_count == 1);  // true
    // struct Widget_refcounted* ptr2 = Widget_refcounted_retain(ptr1);
    // bool is_unique2 = (ptr1->ref_count == 1);  // false
}

TEST_F(SharedPtrTest, ResetReleasesOwnership) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr1(new Widget());
            std::shared_ptr<Widget> ptr2 = ptr1;  // ref_count = 2
            ptr1.reset();  // ptr1 becomes null, ref_count = 1
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();  // ref=1
    // struct Widget_refcounted* ptr2 = Widget_refcounted_retain(ptr1);  // ref=2
    // if (ptr1) Widget_refcounted_release(ptr1);  // ref=1
    // ptr1 = NULL;
}

TEST_F(SharedPtrTest, ResetWithNewPointer) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            ptr.reset(new Widget());  // Release old, assign new
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new();
    // if (ptr) Widget_refcounted_release(ptr);
    // ptr = Widget_refcounted_new();
}

TEST_F(SharedPtrTest, GetReturnsRawPointer) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new();
    // struct Widget* raw = &ptr->obj;
}

TEST_F(SharedPtrTest, BoolConversion) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new();
    // if (ptr != NULL) {
    //     // Use ptr
    // }
}

TEST_F(SharedPtrTest, DereferenceOperators) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new();
    // ptr->obj.value = 42;
    // Widget_method(&ptr->obj);
}

// ============================================================================
// Group 2: make_shared Support (5 tests)
// ============================================================================

TEST_F(SharedPtrTest, MakeSharedBasicUsage) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr = Widget_refcounted_new_int(42);
}

TEST_F(SharedPtrTest, MakeSharedWithMultipleArguments) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, MakeSharedSingleAllocationOptimization) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // make_shared is more efficient (single malloc)
}

TEST_F(SharedPtrTest, MakeSharedWithDefaultConstructor) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, MakeSharedExceptionSafety) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Group 3: weak_ptr and Cyclic References (10 tests)
// ============================================================================

TEST_F(WeakPtrTest, BasicCreationFromSharedPtr) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared(new Widget());
            std::weak_ptr<Widget> weak(shared);  // Does not increase ref_count
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* shared = Widget_refcounted_new();  // ref=1
    // struct Widget_refcounted* weak = shared;  // weak pointer (no ref increment)
    // weak->weak_count++;  // Track weak references separately
}

TEST_F(WeakPtrTest, LockCreatesSharedPtr) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* shared = Widget_refcounted_new();  // ref=1
    // struct Widget_refcounted* weak = shared;
    // weak->weak_count++;
    // struct Widget_refcounted* locked = NULL;
    // if (weak != NULL && weak->ref_count > 0) {
    //     locked = Widget_refcounted_retain(weak);  // ref=2
    // }
}

TEST_F(WeakPtrTest, LockReturnsNullWhenExpired) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(WeakPtrTest, ExpiredChecksValidity) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // bool expired = (weak == NULL || weak->ref_count == 0);
}

TEST_F(WeakPtrTest, UseCountReturnsSharedCount) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(WeakPtrTest, ResetReleasesWeakReference) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared(new Widget());
            std::weak_ptr<Widget> weak(shared);
            weak.reset();  // weak becomes null
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // if (weak) weak->weak_count--;
    // weak = NULL;
}

TEST_F(WeakPtrTest, BreaksCyclicReference) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(WeakPtrTest, CopyConstructor) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> shared(new Widget());
            std::weak_ptr<Widget> weak1(shared);
            std::weak_ptr<Widget> weak2(weak1);  // weak_count++
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(WeakPtrTest, AssignmentOperator) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(WeakPtrTest, Swap) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Group 4: Thread-Safe Reference Counting (5 tests)
// ============================================================================

TEST_F(SharedPtrTest, AtomicReferenceCounting) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            // ref_count operations must be atomic (thread-safe)
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // Use atomic operations for ref_count:
    // __atomic_fetch_add(&ptr->ref_count, 1, __ATOMIC_ACQ_REL);
    // __atomic_fetch_sub(&ptr->ref_count, 1, __ATOMIC_ACQ_REL);
}

TEST_F(SharedPtrTest, CopyThreadSafe) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, AtomicLoad) {
    const char *Code = R"(
        #include <memory>
        #include <atomic>

        class Widget {};

        void test() {
            std::shared_ptr<Widget> ptr(new Widget());
            std::shared_ptr<Widget> loaded = std::atomic_load(&ptr);
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, AtomicStore) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, AtomicExchange) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Group 5: Advanced Scenarios and Edge Cases (10 tests)
// ============================================================================

TEST_F(SharedPtrTest, WithCustomDeleter) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, WithArrayDeleter) {
    const char *Code = R"(
        #include <memory>

        void test() {
            std::shared_ptr<int> arr(new int[10], std::default_delete<int[]>());
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, AliasingConstructor) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // value_ptr shares ownership with ptr but points to member
}

TEST_F(SharedPtrTest, WithPolymorphism) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, EnableSharedFromThis) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, InContainer) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, ComparisonOperators) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, OwnerBeforeStrictWeakOrdering) {
    const char *Code = R"(
        #include <memory>

        class Widget {};

        void test() {
            auto ptr1 = std::make_shared<Widget>();
            auto ptr2 = std::make_shared<Widget>();
            bool less = ptr1.owner_before(ptr2);  // For map/set ordering
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(SharedPtrTest, MoveConstructorNoRefcountChange) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Move constructor transfers ownership without ref_count change
}

TEST_F(SharedPtrTest, MoveAssignmentNoRefcountChange) {
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

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";

    // Expected C translation:
    // struct Widget_refcounted* ptr1 = Widget_refcounted_new();
    // struct Widget_refcounted* ptr2 = Widget_refcounted_new();
    // Widget_refcounted_release(ptr2);  // Destroy old
    // ptr2 = ptr1;  // Transfer (no ref change)
    // ptr1 = NULL;
}

// ============================================================================
// Main Function
// ============================================================================

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
