// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/smart_pointers/SharedPtrTest.cpp
// Implementation file

#include "SharedPtrTest.h"

static void SharedPtrTest__ctor_default(struct SharedPtrTest * this) {
}

static void SharedPtrTest__ctor_copy(struct SharedPtrTest * this, const struct SharedPtrTest * other) {
}

void SharedPtrTest_SetUp(struct SharedPtrTest * this) {
}

void SharedPtrTest_TearDown(struct SharedPtrTest * this) {
}

int SharedPtrTest_buildAST(struct SharedPtrTest * this, const char * code) {
}

static void WeakPtrTest__ctor_default(struct WeakPtrTest * this) {
}

static void WeakPtrTest__ctor_copy(struct WeakPtrTest * this, const struct WeakPtrTest * other) {
}

void WeakPtrTest_SetUp(struct WeakPtrTest * this) {
}

void WeakPtrTest_TearDown(struct WeakPtrTest * this) {
}

int WeakPtrTest_buildAST(struct WeakPtrTest * this, const char * code) {
}

int TEST_F(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n        };\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n        }  // ref_count-- (destruction if count reaches 0)\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());  // ref_count = 1\n            std::shared_ptr<Widget> ptr2(ptr1);           // ref_count = 2\n        }  // ptr2 destroyed (ref_count = 1), ptr1 destroyed (ref_count = 0, delete object)\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_1(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());\n            std::shared_ptr<Widget> ptr2(new Widget());\n            ptr2 = ptr1;  // Destroys ptr2's old object, shares ptr1's object\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_2(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());\n            long count1 = ptr1.use_count();  // 1\n\n            std::shared_ptr<Widget> ptr2 = ptr1;\n            long count2 = ptr1.use_count();  // 2\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_3(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());\n            bool is_unique1 = ptr1.unique();  // true (ref_count == 1)\n\n            std::shared_ptr<Widget> ptr2 = ptr1;\n            bool is_unique2 = ptr1.unique();  // false (ref_count == 2)\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_4(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());\n            std::shared_ptr<Widget> ptr2 = ptr1;  // ref_count = 2\n            ptr1.reset();  // ptr1 becomes null, ref_count = 1\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_5(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            ptr.reset(new Widget());  // Release old, assign new\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_6(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n        };\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            Widget* raw = ptr.get();\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_7(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            if (ptr) {\n                // Use ptr\n            }\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_8(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n            void method() {}\n        };\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            ptr->value = 42;\n            (*ptr).method();\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_9(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n            Widget(int v) : value(v) {}\n        };\n\n        void test() {\n            auto ptr = std::make_shared<Widget>(42);\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_10(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int x, y;\n            Widget(int a, int b) : x(a), y(b) {}\n        };\n\n        void test() {\n            auto ptr = std::make_shared<Widget>(10, 20);\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_11(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            // make_shared: single allocation (object + control block)\n            auto ptr1 = std::make_shared<Widget>();\n\n            // shared_ptr: two allocations (object, then control block)\n            std::shared_ptr<Widget> ptr2(new Widget());\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_12(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            Widget() = default;\n        };\n\n        void test() {\n            auto ptr = std::make_shared<Widget>();\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_13(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            Widget(int v) {}\n        };\n\n        void process(std::shared_ptr<Widget> p1, std::shared_ptr<Widget> p2) {}\n\n        void test() {\n            // make_shared is exception-safe\n            process(std::make_shared<Widget>(1), std::make_shared<Widget>(2));\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared(new Widget());\n            std::weak_ptr<Widget> weak(shared);  // Does not increase ref_count\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_1(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared(new Widget());\n            std::weak_ptr<Widget> weak(shared);\n\n            std::shared_ptr<Widget> locked = weak.lock();  // ref_count++\n            // locked is valid while shared exists\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_2(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::weak_ptr<Widget> weak;\n            {\n                std::shared_ptr<Widget> shared(new Widget());\n                weak = shared;\n            }  // shared destroyed, object deleted\n\n            std::shared_ptr<Widget> locked = weak.lock();  // Returns null\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_3(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::weak_ptr<Widget> weak;\n            {\n                std::shared_ptr<Widget> shared(new Widget());\n                weak = shared;\n                bool expired1 = weak.expired();  // false\n            }\n            bool expired2 = weak.expired();  // true\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_4(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared1(new Widget());\n            std::weak_ptr<Widget> weak(shared1);\n\n            long count1 = weak.use_count();  // 1\n\n            std::shared_ptr<Widget> shared2 = shared1;\n            long count2 = weak.use_count();  // 2\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_5(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared(new Widget());\n            std::weak_ptr<Widget> weak(shared);\n            weak.reset();  // weak becomes null\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_6(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Node {\n        public:\n            std::shared_ptr<Node> next;\n            std::weak_ptr<Node> prev;  // Weak to break cycle\n        };\n\n        void test() {\n            auto node1 = std::make_shared<Node>();\n            auto node2 = std::make_shared<Node>();\n            node1->next = node2;\n            node2->prev = node1;  // No cycle (weak_ptr)\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_7(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared(new Widget());\n            std::weak_ptr<Widget> weak1(shared);\n            std::weak_ptr<Widget> weak2(weak1);  // weak_count++\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_8(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared1(new Widget());\n            std::shared_ptr<Widget> shared2(new Widget());\n            std::weak_ptr<Widget> weak1(shared1);\n            std::weak_ptr<Widget> weak2(shared2);\n            weak2 = weak1;  // weak2 now observes shared1's object\n        }\n    ";

	auto AST;

}

int TEST_F_WeakPtrTest_int_9(struct WeakPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> shared1(new Widget());\n            std::shared_ptr<Widget> shared2(new Widget());\n            std::weak_ptr<Widget> weak1(shared1);\n            std::weak_ptr<Widget> weak2(shared2);\n            weak1.swap(weak2);\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_14(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            // ref_count operations must be atomic (thread-safe)\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_15(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <thread>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n\n            std::thread t1([ptr]() {\n                std::shared_ptr<Widget> local = ptr;  // Atomic ref_count++\n            });\n\n            std::thread t2([ptr]() {\n                std::shared_ptr<Widget> local = ptr;  // Atomic ref_count++\n            });\n\n            t1.join();\n            t2.join();\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_16(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <atomic>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            std::shared_ptr<Widget> loaded = std::atomic_load(&ptr);\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_17(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <atomic>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr;\n            std::shared_ptr<Widget> new_ptr(new Widget());\n            std::atomic_store(&ptr, new_ptr);\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_18(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <atomic>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            std::shared_ptr<Widget> new_ptr(new Widget());\n            std::shared_ptr<Widget> old_ptr = std::atomic_exchange(&ptr, new_ptr);\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_19(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        struct Resource {};\n\n        void custom_deleter(Resource* res) {\n            // Custom cleanup\n        }\n\n        void test() {\n            std::shared_ptr<Resource> ptr(new Resource(), custom_deleter);\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_20(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        void test() {\n            std::shared_ptr<int> arr(new int[10], std::default_delete<int[]>());\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_21(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        struct Widget {\n            int value;\n        };\n\n        void test() {\n            std::shared_ptr<Widget> ptr(new Widget());\n            std::shared_ptr<int> value_ptr(ptr, &ptr->value);  // Shares ownership\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_22(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Base {\n        public:\n            virtual ~Base() = default;\n        };\n\n        class Derived : public Base {};\n\n        void test() {\n            std::shared_ptr<Base> ptr = std::make_shared<Derived>();\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_23(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget : public std::enable_shared_from_this<Widget> {\n        public:\n            std::shared_ptr<Widget> get_shared() {\n                return shared_from_this();\n            }\n        };\n\n        void test() {\n            auto ptr = std::make_shared<Widget>();\n            auto ptr2 = ptr->get_shared();  // Same object, ref_count++\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_24(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <vector>\n\n        class Widget {};\n\n        void test() {\n            std::vector<std::shared_ptr<Widget>> vec;\n            vec.push_back(std::make_shared<Widget>());\n            vec.push_back(vec[0]);  // ref_count++\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_25(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            auto ptr1 = std::make_shared<Widget>();\n            auto ptr2 = std::make_shared<Widget>();\n            auto ptr3 = ptr1;\n\n            bool eq = (ptr1 == ptr3);  // true (same object)\n            bool ne = (ptr1 != ptr2);  // true (different objects)\n            bool null_check = (ptr1 == nullptr);  // false\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_26(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            auto ptr1 = std::make_shared<Widget>();\n            auto ptr2 = std::make_shared<Widget>();\n            bool less = ptr1.owner_before(ptr2);  // For map/set ordering\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_27(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <utility>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());  // ref=1\n            std::shared_ptr<Widget> ptr2(std::move(ptr1));  // ref=1 (no change)\n            // ptr1 is now null\n        }\n    ";

	auto AST;

}

int TEST_F_SharedPtrTest_int_28(struct SharedPtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <utility>\n\n        class Widget {};\n\n        void test() {\n            std::shared_ptr<Widget> ptr1(new Widget());  // ref=1\n            std::shared_ptr<Widget> ptr2(new Widget());  // ref=1\n            ptr2 = std::move(ptr1);  // ptr2's old object destroyed, ptr1 transferred\n        }\n    ";

	auto AST;

}

int main(int argc, char * * argv) {
}

