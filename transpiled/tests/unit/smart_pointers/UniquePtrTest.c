// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/smart_pointers/UniquePtrTest.cpp
// Implementation file

#include "UniquePtrTest.h"

static void UniquePtrTest__ctor_default(struct UniquePtrTest * this) {
}

static void UniquePtrTest__ctor_copy(struct UniquePtrTest * this, const struct UniquePtrTest * other) {
}

void UniquePtrTest_SetUp(struct UniquePtrTest * this) {
}

void UniquePtrTest_TearDown(struct UniquePtrTest * this) {
}

int UniquePtrTest_buildAST(struct UniquePtrTest * this, const char * code) {
}

int TEST_F(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n        };\n\n        void test() {\n            std::unique_ptr<Widget> ptr(new Widget());\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr(nullptr);\n            std::unique_ptr<Widget> ptr2;  // Default-constructed (nullptr)\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_1(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n        };\n\n        void test() {\n            std::unique_ptr<Widget> ptr(new Widget());\n            Widget* raw = ptr.get();\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_2(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n        };\n\n        void test() {\n            std::unique_ptr<Widget> ptr(new Widget());\n            ptr.reset(new Widget());  // Destroys old, assigns new\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_3(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr(new Widget());\n            ptr.reset();  // Destroys and sets to nullptr\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_4(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr(new Widget());\n            Widget* raw = ptr.release();  // No destruction, ownership transferred\n            delete raw;\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_5(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr(new Widget());\n            if (ptr) {\n                // Use ptr\n            }\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_6(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n            void method() {}\n        };\n\n        void test() {\n            std::unique_ptr<Widget> ptr(new Widget());\n            ptr->value = 42;\n            (*ptr).method();\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_7(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <utility>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr1(new Widget());\n            std::unique_ptr<Widget> ptr2(std::move(ptr1));  // ptr1 becomes null\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_8(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <utility>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr1(new Widget());\n            std::unique_ptr<Widget> ptr2(new Widget());\n            ptr2 = std::move(ptr1);  // Destroys ptr2's old object\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_9(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        std::unique_ptr<Widget> create() {\n            return std::unique_ptr<Widget>(new Widget());\n        }\n\n        void test() {\n            std::unique_ptr<Widget> ptr = create();\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_10(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <utility>\n\n        class Widget {};\n\n        void consume(std::unique_ptr<Widget> ptr) {\n            // Takes ownership\n        }\n\n        void test() {\n            std::unique_ptr<Widget> ptr(new Widget());\n            consume(std::move(ptr));  // ptr becomes null\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_11(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr1(new Widget());\n            // std::unique_ptr<Widget> ptr2 = ptr1;  // ERROR: copy constructor deleted\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_12(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr1(new Widget());\n            std::unique_ptr<Widget> ptr2(new Widget());\n            // ptr2 = ptr1;  // ERROR: copy assignment deleted\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_13(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr1(new Widget());\n            std::unique_ptr<Widget> ptr2(new Widget());\n            ptr1.swap(ptr2);  // Exchange ownership\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_14(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int value;\n            Widget(int v) : value(v) {}\n        };\n\n        void test() {\n            auto ptr = std::make_unique<Widget>(42);\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_15(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            int x, y;\n            Widget(int a, int b) : x(a), y(b) {}\n        };\n\n        void test() {\n            auto ptr = std::make_unique<Widget>(10, 20);\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_16(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            Widget() = default;\n        };\n\n        void test() {\n            auto ptr = std::make_unique<Widget>();\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_17(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {\n        public:\n            Widget(int v) {}\n        };\n\n        void test() {\n            // make_unique is exception-safe (single allocation)\n            auto ptr1 = std::make_unique<Widget>(42);\n\n            // unique_ptr constructor (two allocations - Widget and control block)\n            std::unique_ptr<Widget> ptr2(new Widget(42));\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_18(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        void test() {\n            auto ptr = std::make_unique<int[]>(10);  // Array of 10 ints\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_19(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        struct Resource {\n            int handle;\n        };\n\n        void custom_deleter(Resource* res) {\n            // Custom cleanup\n        }\n\n        void test() {\n            std::unique_ptr<Resource, void(*)(Resource*)> ptr(\n                new Resource(), custom_deleter\n            );\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_20(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        struct Resource {\n            int handle;\n        };\n\n        void test() {\n            auto deleter = [](Resource* res) {\n                // Custom cleanup\n            };\n            std::unique_ptr<Resource, decltype(deleter)> ptr(\n                new Resource(), deleter\n            );\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_21(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        struct Resource {\n            int handle;\n        };\n\n        struct FileDeleter {\n            int log_fd;\n            void operator()(Resource* res) const {\n                // Log to log_fd, then delete\n            }\n        };\n\n        void test() {\n            std::unique_ptr<Resource, FileDeleter> ptr(\n                new Resource(), FileDeleter{3}\n            );\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_22(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <cstdio>\n\n        void test() {\n            std::unique_ptr<FILE, decltype(&fclose)> file(\n                fopen(\"test.txt\", \"r\"), &fclose\n            );\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_23(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        void test() {\n            std::unique_ptr<int[]> arr(new int[10]);  // Uses delete[] automatically\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_24(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <functional>\n\n        struct Resource {};\n\n        struct Deleter {\n            void operator()(Resource* res) const {}\n        };\n\n        void test() {\n            Deleter d;\n            std::unique_ptr<Resource, std::reference_wrapper<Deleter>> ptr(\n                new Resource(), std::ref(d)\n            );\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_25(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n        #include <vector>\n\n        class Widget {};\n\n        void test() {\n            std::vector<std::unique_ptr<Widget>> vec;\n            vec.push_back(std::make_unique<Widget>());\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_26(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Resource {};\n\n        class Owner {\n        private:\n            std::unique_ptr<Resource> resource;\n        public:\n            Owner() : resource(std::make_unique<Resource>()) {}\n        };\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_27(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Base {\n        public:\n            virtual ~Base() = default;\n        };\n\n        class Derived : public Base {};\n\n        void test() {\n            std::unique_ptr<Base> ptr = std::make_unique<Derived>();\n        }\n    ";

	auto AST;

}

int TEST_F_UniquePtrTest_int_28(struct UniquePtrTest, int) {
	const char *Code = "\n        #include <memory>\n\n        class Widget {};\n\n        void test() {\n            std::unique_ptr<Widget> ptr1(new Widget());\n            std::unique_ptr<Widget> ptr2(new Widget());\n            std::unique_ptr<Widget> ptr3;\n\n            bool eq = (ptr1 == ptr2);\n            bool ne = (ptr1 != ptr2);\n            bool lt = (ptr1 < ptr2);\n            bool null_check = (ptr3 == nullptr);\n        }\n    ";

	auto AST;

}

int main(int argc, char * * argv) {
}

