// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/smart_pointers/SharedPtrTest_old.cpp
// Implementation file

#include "SharedPtrTest_old.h"

void test_shared_ptr_basic_constructor() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n        };\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n        }  // ref_count-- (destruction if count reaches 0)\n    ";

	auto AST;

}

void test_shared_ptr_copy_constructor_increments_refcount() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());  // ref_count = 1\n            std::shared_ptr<Widget> ptr2(ptr1);           // ref_count = 2\n        }  // ptr2 destroyed (ref_count = 1), ptr1 destroyed (ref_count = 0, delete object)\n    ";

	auto AST;

}

void test_shared_ptr_copy_assignment_increments_refcount() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());\n            std::shared_ptr<Widget> ptr2(new Widget());\n            ptr2 = ptr1;  // Destroys ptr2's old object, shares ptr1's object\n        }\n    ";

	auto AST;

}

void test_shared_ptr_use_count_returns_ref_count() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());\n            long count1 = ptr1.use_count();  // 1\n\n            std::shared_ptr<Widget> ptr2 = ptr1;\n            long count2 = ptr1.use_count();  // 2\n        }\n    ";

	auto AST;

}

void test_shared_ptr_unique_checks_sole_ownership() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());\n            bool is_unique1 = ptr1.unique();  // true (ref_count == 1)\n\n            std::shared_ptr<Widget> ptr2 = ptr1;\n            bool is_unique2 = ptr1.unique();  // false (ref_count == 2)\n        }\n    ";

	auto AST;

}

void test_shared_ptr_reset_releases_ownership() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());\n            std::shared_ptr<Widget> ptr2 = ptr1;  // ref_count = 2\n            ptr1.reset();  // ptr1 becomes null, ref_count = 1\n        }\n    ";

	auto AST;

}

void test_shared_ptr_reset_with_new_pointer() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            ptr.reset(new Widget());  // Release old, assign new\n        }\n    ";

	auto AST;

}

void test_shared_ptr_get_returns_raw_pointer() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n        };\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            Widget* raw = ptr.get();\n        }\n    ";

	auto AST;

}

void test_shared_ptr_bool_conversion() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            if (ptr) {\n                // Use ptr\n            }\n        }\n    ";

	auto AST;

}

void test_shared_ptr_dereference_operators() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n            void method() {}\n        };\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            ptr->value = 42;\n            (*ptr).method();\n        }\n    ";

	auto AST;

}

void test_make_shared_basic_usage() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n            Widget(int v) : value(v) {}\n        };\n\n        void test() {\n            auto ptr = std::make_shared<Widget>(42);\n        }\n    ";

	auto AST;

}

void test_make_shared_with_multiple_arguments() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int x, y;\n            Widget(int a, int b) : x(a), y(b) {}\n        };\n\n        void test() {\n            auto ptr = std::make_shared<Widget>(10, 20);\n        }\n    ";

	auto AST;

}

void test_make_shared_single_allocation_optimization() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            // make_shared: single allocation (object + control block)\n            auto ptr1 = std::make_shared<Widget>();\n\n            // shared_ptr: two allocations (object, then control block)\n            std::shared_ptr<Widget> ptr2(new Widget());\n        }\n    ";

	auto AST;

}

void test_make_shared_with_default_constructor() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            Widget() = default;\n        };\n\n        void test() {\n            auto ptr = std::make_shared<Widget>();\n        }\n    ";

	auto AST;

}

void test_make_shared_exception_safety() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            Widget(int v) {}\n        };\n\n        void process(std::shared_ptr<Widget> p1, std::shared_ptr<Widget> p2) {}\n\n        void test() {\n            // make_shared is exception-safe\n            process(std::make_shared<Widget>(1), std::make_shared<Widget>(2));\n        }\n    ";

	auto AST;

}

void test_weak_ptr_basic_creation_from_shared_ptr() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared(new Widget());\n            std::weak_ptr<Widget> weak(shared);  // Does not increase ref_count\n        }\n    ";

	auto AST;

}

void test_weak_ptr_lock_creates_shared_ptr() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared(new Widget());\n            std::weak_ptr<Widget> weak(shared);\n\n            std::shared_ptr<Widget> locked = weak.lock();  // ref_count++\n            // locked is valid while shared exists\n        }\n    ";

	auto AST;

}

void test_weak_ptr_lock_returns_null_when_expired() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::weak_ptr<Widget> weak;\n            {\n                std::shared_ptr<Widget> shared(new Widget());\n                weak = shared;\n            }  // shared destroyed, object deleted\n\n            std::shared_ptr<Widget> locked = weak.lock();  // Returns null\n        }\n    ";

	auto AST;

}

void test_weak_ptr_expired_checks_validity() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::weak_ptr<Widget> weak;\n            {\n                std::shared_ptr<Widget> shared(new Widget());\n                weak = shared;\n                bool expired1 = weak.expired();  // false\n            }\n            bool expired2 = weak.expired();  // true\n        }\n    ";

	auto AST;

}

void test_weak_ptr_use_count_returns_shared_count() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared1(new Widget());\n            std::weak_ptr<Widget> weak(shared1);\n\n            long count1 = weak.use_count();  // 1\n\n            std::shared_ptr<Widget> shared2 = shared1;\n            long count2 = weak.use_count();  // 2\n        }\n    ";

	auto AST;

}

void test_weak_ptr_reset_releases_weak_reference() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared(new Widget());\n            std::weak_ptr<Widget> weak(shared);\n            weak.reset();  // weak becomes null\n        }\n    ";

	auto AST;

}

void test_weak_ptr_breaks_cyclic_reference() {
	const char *Code = "\n        #include <memory>\n\n        class Node {\n        public:\n            std::shared_ptr<Node> next;\n            std::weak_ptr<Node> prev;  // Weak to break cycle\n        };\n\n        void test() {\n            auto node1 = std::make_shared<Node>();\n            auto node2 = std::make_shared<Node>();\n            node1->next = node2;\n            node2->prev = node1;  // No cycle (weak_ptr)\n        }\n    ";

	auto AST;

}

void test_weak_ptr_copy_constructor() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared(new Widget());\n            std::weak_ptr<Widget> weak1(shared);\n            std::weak_ptr<Widget> weak2(weak1);  // weak_count++\n        }\n    ";

	auto AST;

}

void test_weak_ptr_assignment_operator() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared1(new Widget());\n            std::shared_ptr<Widget> shared2(new Widget());\n            std::weak_ptr<Widget> weak1(shared1);\n            std::weak_ptr<Widget> weak2(shared2);\n            weak2 = weak1;  // weak2 now observes shared1's object\n        }\n    ";

	auto AST;

}

void test_weak_ptr_swap() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared1(new Widget());\n            std::shared_ptr<Widget> shared2(new Widget());\n            std::weak_ptr<Widget> weak1(shared1);\n            std::weak_ptr<Widget> weak2(shared2);\n            weak1.swap(weak2);\n        }\n    ";

	auto AST;

}

void test_shared_ptr_atomic_reference_counting() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            // ref_count operations must be atomic (thread-safe)\n        }\n    ";

	auto AST;

}

void test_shared_ptr_copy_thread_safe() {
	const char *Code = "\n        #include <memory>\n        #include <thread>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n\n            std::thread t1([ptr]() {\n                std::shared_ptr<Widget> local = ptr;  // Atomic ref_count++\n            });\n\n            std::thread t2([ptr]() {\n                std::shared_ptr<Widget> local = ptr;  // Atomic ref_count++\n            });\n\n            t1.join();\n            t2.join();\n        }\n    ";

	auto AST;

}

void test_atomic_load_shared_ptr() {
	const char *Code = "\n        #include <memory>\n        #include <atomic>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            std::shared_ptr<Widget> loaded = std::atomic_load(&ptr);\n        }\n    ";

	auto AST;

}

void test_atomic_store_shared_ptr() {
	const char *Code = "\n        #include <memory>\n        #include <atomic>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr;\n            std::shared_ptr<Widget> new_ptr(new Widget());\n            std::atomic_store(&ptr, new_ptr);\n        }\n    ";

	auto AST;

}

void test_atomic_exchange_shared_ptr() {
	const char *Code = "\n        #include <memory>\n        #include <atomic>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            std::shared_ptr<Widget> new_ptr(new Widget());\n            std::shared_ptr<Widget> old_ptr = std::atomic_exchange(&ptr, new_ptr);\n        }\n    ";

	auto AST;

}

void test_shared_ptr_with_custom_deleter() {
	const char *Code = "\n        #include <memory>\n\n        struct Resource {};\n\n        void custom_deleter(Resource* res) {\n            // Custom cleanup\n        }\n\n        void test() {\n            std::shared_ptr<Resource> ptr(new Resource(), custom_deleter);\n        }\n    ";

	auto AST;

}

void test_shared_ptr_with_array_deleter() {
	const char *Code = "\n        #include <memory>\n\n        void test() {\n            std::shared_ptr<int> arr(new int[10], std::default_delete<int[]>());\n        }\n    ";

	auto AST;

}

void test_shared_ptr_aliasing_constructor() {
	const char *Code = "\n        #include <memory>\n\n        struct Widget {\n            int value;\n        };\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            std::shared_ptr<int> value_ptr(ptr, &ptr->value);  // Shares ownership\n        }\n    ";

	auto AST;

}

void test_shared_ptr_with_polymorphism() {
	const char *Code = "\n        #include <memory>\n\n        class Base {\n        public:\n            virtual ~Base() = default;\n        };\n\n        class Derived : public Base {};\n\n        void test() {\n            std::shared_ptr<Base> ptr = std::make_shared<Derived>();\n        }\n    ";

	auto AST;

}

void test_shared_ptr_enable_shared_from_this() {
	const char *Code = "\n        #include <memory>\n\n        class Widget : public std::enable_shared_from_this<Widget> {\n        public:\n            std::shared_ptr<Widget> get_shared() {\n                return shared_from_this();\n            }\n        };\n\n        void test() {\n            auto ptr = std::make_shared<Widget>();\n            auto ptr2 = ptr->get_shared();  // Same object, ref_count++\n        }\n    ";

	auto AST;

}

void test_shared_ptr_in_container() {
	const char *Code = "\n        #include <memory>\n        #include <vector>\n\n        class Widget {};\n\n        void test() {\n            std::vector<std::shared_ptr<Widget>> vec;\n            vec.push_back(std::make_shared<Widget>());\n            vec.push_back(vec[0]);  // ref_count++\n        }\n    ";

	auto AST;

}

void test_shared_ptr_comparison_operators() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            auto ptr1 = std::make_shared<Widget>();\n            auto ptr2 = std::make_shared<Widget>();\n            auto ptr3 = ptr1;\n\n            bool eq = (ptr1 == ptr3);  // true (same object)\n            bool ne = (ptr1 != ptr2);  // true (different objects)\n            bool null_check = (ptr1 == nullptr);  // false\n        }\n    ";

	auto AST;

}

void test_shared_ptr_owner_before_strict_weak_ordering() {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            auto ptr1 = std::make_shared<Widget>();\n            auto ptr2 = std::make_shared<Widget>();\n            bool less = ptr1.owner_before(ptr2);  // For map/set ordering\n        }\n    ";

	auto AST;

}

void test_shared_ptr_move_constructor_no_refcount_change() {
	const char *Code = "\n        #include <memory>\n        #include <utility>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());  // ref=1\n            std::shared_ptr<Widget> ptr2(std::move(ptr1));  // ref=1 (no change)\n            // ptr1 is now null\n        }\n    ";

	auto AST;

}

void test_shared_ptr_move_assignment_no_refcount_change() {
	const char *Code = "\n        #include <memory>\n        #include <utility>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());  // ref=1\n            std::shared_ptr<Widget> ptr2(new Widget());  // ref=1\n            ptr2 = std::move(ptr1);  // ptr2's old object destroyed, ptr1 transferred\n        }\n    ";

	auto AST;

}

int main() {
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
	test_make_shared_basic_usage();
	test_make_shared_with_multiple_arguments();
	test_make_shared_single_allocation_optimization();
	test_make_shared_with_default_constructor();
	test_make_shared_exception_safety();
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
	test_shared_ptr_atomic_reference_counting();
	test_shared_ptr_copy_thread_safe();
	test_atomic_load_shared_ptr();
	test_atomic_store_shared_ptr();
	test_atomic_exchange_shared_ptr();
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
	return 0;
;
}

