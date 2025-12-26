// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/MoveSemanticTranslatorTest_gtest.cpp
// Implementation file

#include "MoveSemanticTranslatorTest_gtest.h"

static void MoveSemanticTestFixture__ctor_default(struct MoveSemanticTestFixture * this) {
}

static void MoveSemanticTestFixture__ctor_copy(struct MoveSemanticTestFixture * this, const struct MoveSemanticTestFixture * other) {
}

int MoveSemanticTestFixture_buildAST(struct MoveSemanticTestFixture * this, const char * code) {
}

static void MoveSemanticsFinder__ctor_default(struct MoveSemanticsFinder * this) {
	this->moveConstructors = 0;
	this->moveAssignments = 0;
	this->moveConstructorCalls = 0;
	this->stdMoveCalls = 0;
	this->rvalueRefs = 0;
	this->forwardingFunctions = 0;
}

static void MoveSemanticsFinder__ctor_copy(struct MoveSemanticsFinder * this, const struct MoveSemanticsFinder * other) {
	this->moveConstructors = other->moveConstructors;
	this->moveAssignments = other->moveAssignments;
	this->moveConstructorCalls = other->moveConstructorCalls;
	this->stdMoveCalls = other->stdMoveCalls;
	this->rvalueRefs = other->rvalueRefs;
	this->forwardingFunctions = other->forwardingFunctions;
}

bool MoveSemanticsFinder_VisitCXXConstructorDecl(struct MoveSemanticsFinder * this, int * D) {
	return true;
;
}

bool MoveSemanticsFinder_VisitCXXMethodDecl(struct MoveSemanticsFinder * this, int * D) {
	return true;
;
}

bool MoveSemanticsFinder_VisitCXXConstructExpr(struct MoveSemanticsFinder * this, int * E) {
	return true;
;
}

bool MoveSemanticsFinder_VisitCallExpr(struct MoveSemanticsFinder * this, int * E) {
	return true;
;
}

bool MoveSemanticsFinder_VisitValueDecl(struct MoveSemanticsFinder * this, int * D) {
	return true;
;
}

int TEST_F(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        void process(int&& value) {\n            // Process rvalue reference\n        }\n    ";

	struct MoveSemanticsFinder finder;

	const auto *param = finder()[0];

}

int TEST_F_MoveSemanticTestFixture_int(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int data;\n        public:\n            int&& getData() { return static_cast<int&&>(data); }\n        };\n    ";

	auto *TU;

	int *method;

}

int TEST_F_MoveSemanticTestFixture_int_1(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        void accept_rvalue(int&& value) {}\n\n        void test() {\n            int x = 42;\n            // accept_rvalue(x);  // Should not compile - lvalue binding\n            accept_rvalue(100);   // OK - rvalue binding\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_2(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        int getTemporary() { return 42; }\n\n        void test() {\n            int&& rref = getTemporary();\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_3(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        template<typename T>\n        void func(T&& param) {\n            // T&& is a universal reference\n        }\n\n        void test() {\n            func(42);  // T = int, param is int&&\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_4(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        template<typename T>\n        void func(T&& param) {\n            // Universal reference\n        }\n\n        void test() {\n            int x = 42;\n            func(x);  // T = int&, param is int& (& + && -> &)\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_5(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Container {\n            int&& rref;  // Rvalue reference member (rare but legal)\n        public:\n            Container(int&& r) : rref(static_cast<int&&>(r)) {}\n        };\n    ";

	auto *TU;

	bool foundRvalueRefMember = false;

}

int TEST_F_MoveSemanticTestFixture_int_6(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int value;\n        public:\n            Widget(int v) : value(v) {}\n        };\n\n        void test() {\n            const Widget&& rref = Widget(42);\n            // Temporary's lifetime is extended\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_7(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        void process(int& lvalue) {}\n        void process(int&& rvalue) {}\n\n        void test() {\n            int x = 42;\n            process(x);    // Calls lvalue version\n            process(100);  // Calls rvalue version\n        }\n    ";

	auto *TU;

	int processCount = 0;

}

int TEST_F_MoveSemanticTestFixture_int_8(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        void test() {\n            int x = 42;\n            int&& rref = static_cast<int&&>(x);\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_9(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int* data;\n        public:\n            Widget(Widget&& other) : data(other.data) {\n                other.data = nullptr;\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_10(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int* data;\n        public:\n            Widget& operator=(Widget&& other) {\n                if (this != &other) {\n                    delete data;\n                    data = other.data;\n                    other.data = nullptr;\n                }\n                return *this;\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_11(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int value;\n            // Compiler generates default move constructor\n        };\n\n        void test() {\n            Widget w1;\n            Widget w2(static_cast<Widget&&>(w1));\n        }\n    ";

	auto *TU;

	int *WidgetClass;

}

int TEST_F_MoveSemanticTestFixture_int_12(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class NonMovable {\n        public:\n            NonMovable(NonMovable&&) = delete;\n        };\n    ";

	auto *TU;

	int *moveConstructor;

}

int TEST_F_MoveSemanticTestFixture_int_13(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int* data;\n        public:\n            Widget(Widget&& other) noexcept : data(other.data) {\n                other.data = nullptr;\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

	const auto *moveCtor = finder()[0];

	auto exceptionSpec;
}

int TEST_F_MoveSemanticTestFixture_int_14(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int* data;\n        public:\n            Widget& operator=(Widget&& other) noexcept {\n                if (this != &other) {\n                    delete data;\n                    data = other.data;\n                    other.data = nullptr;\n                }\n                return *this;\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_15(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Inner {\n        public:\n            Inner(Inner&&) noexcept = default;\n        };\n\n        class Outer {\n            Inner inner1;\n            Inner inner2;\n        public:\n            Outer(Outer&& other) noexcept\n                : inner1(static_cast<Inner&&>(other.inner1)),\n                  inner2(static_cast<Inner&&>(other.inner2)) {}\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_16(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Resource {\n            int* buffer;\n            int size;\n        public:\n            Resource(Resource&& other) noexcept\n                : buffer(other.buffer), size(other.size) {\n                other.buffer = nullptr;\n                other.size = 0;\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_17(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Resource {\n            int* buffer;\n        public:\n            Resource& operator=(Resource&& other) noexcept {\n                if (this != &other) {\n                    delete[] buffer;  // Clean up existing resource\n                    buffer = other.buffer;\n                    other.buffer = nullptr;\n                }\n                return *this;\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_18(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Base {\n        public:\n            Base(Base&&) noexcept = default;\n        };\n\n        class Derived : public Base {\n        public:\n            Derived(Derived&& other) noexcept\n                : Base(static_cast<Base&&>(other)) {}\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_19(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class MoveOnly {\n        public:\n            MoveOnly() = default;\n            MoveOnly(const MoveOnly&) = delete;\n            MoveOnly& operator=(const MoveOnly&) = delete;\n            MoveOnly(MoveOnly&&) noexcept = default;\n            MoveOnly& operator=(MoveOnly&&) noexcept = default;\n        };\n    ";

	auto *TU;

	int *MoveOnlyClass;

}

int TEST_F_MoveSemanticTestFixture_int_20(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class SafeMove {\n            int* data;\n        public:\n            SafeMove(SafeMove&& other) noexcept\n                : data(other.data) {\n                other.data = nullptr;\n                // No throwing operations\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_21(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        void test() {\n            int x = 42;\n            int&& rref = std::move(x);\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_22(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        class Widget {\n            int* data;\n        public:\n            Widget clone() {\n                Widget temp;\n                return std::move(temp);\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_23(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        void consume(int&& value) {}\n\n        void test() {\n            int x = 42;\n            consume(std::move(x));\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_24(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        class Inner {\n        public:\n            Inner(Inner&&) = default;\n        };\n\n        class Outer {\n            Inner inner;\n        public:\n            Outer(Inner&& i) : inner(std::move(i)) {}\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_25(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n        #include <vector>\n\n        class Widget {\n        public:\n            Widget(Widget&&) = default;\n        };\n\n        void test() {\n            std::vector<Widget> vec;\n            Widget w;\n            vec.push_back(std::move(w));\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_26(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n        #include <memory>\n\n        void test() {\n            std::unique_ptr<int> p1(new int(42));\n            std::unique_ptr<int> p2 = std::move(p1);\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_27(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        void test() {\n            const int x = 42;\n            // std::move on const returns const int&&\n            // which binds to const int&, not int&&\n            auto&& result = std::move(x);\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_28(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        class Widget {\n        public:\n            Widget(Widget&&) = default;\n        };\n\n        Widget createWidget() {\n            Widget w1;\n            Widget w2(std::move(w1));\n            Widget w3(std::move(w2));\n            return std::move(w3);\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_29(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        class Widget {\n        public:\n            Widget(Widget&&) = default;\n        };\n\n        Widget createWidget() {\n            return Widget();  // Already an rvalue, std::move unnecessary\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_30(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        class Widget {\n            int* data;\n        public:\n            int* release() {\n                int* temp = data;\n                data = nullptr;\n                return std::move(temp);  // std::move on pointer (no effect but legal)\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_31(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n        #include <vector>\n\n        class Widget {\n        public:\n            Widget(Widget&&) = default;\n        };\n\n        void processAll(std::vector<Widget>& vec) {\n            for (auto& w : vec) {\n                Widget moved = std::move(w);\n            }\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_32(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        template<typename T>\n        void swap(T& a, T& b) {\n            T temp = std::move(a);\n            a = std::move(b);\n            b = std::move(temp);\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_33(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        template<typename T>\n        void wrapper(T&& arg) {\n            process(std::forward<T>(arg));\n        }\n\n        void process(int&) {}\n        void process(int&&) {}\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_34(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        template<typename T>\n        void func(T&& param) {\n            // T&& is a universal reference (forwarding reference)\n        }\n\n        void test() {\n            int x = 42;\n            func(x);    // T = int&\n            func(100);  // T = int\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_35(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        class Widget {\n        public:\n            Widget(int&& value) {}\n            Widget(const int& value) {}\n        };\n\n        template<typename T>\n        Widget makeWidget(T&& value) {\n            return Widget(std::forward<T>(value));\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_36(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        template<typename... Args>\n        void forwardAll(Args&&... args) {\n            process(std::forward<Args>(args)...);\n        }\n\n        void process(int, double, char) {}\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_37(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n        #include <vector>\n\n        class Widget {\n        public:\n            Widget(int, double) {}\n        };\n\n        void test() {\n            std::vector<Widget> vec;\n            vec.emplace_back(42, 3.14);\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_38(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        template<typename T>\n        void wrapper(T&& arg) {\n            process(std::forward<T>(arg));\n        }\n\n        void process(int& lvalue) {}\n\n        void test() {\n            int x = 42;\n            wrapper(x);  // Should preserve lvalue-ness\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_39(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        template<typename T>\n        void wrapper(T&& arg) {\n            process(std::forward<T>(arg));\n        }\n\n        void process(int&& rvalue) {}\n\n        void test() {\n            wrapper(42);  // Should preserve rvalue-ness\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_40(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <memory>\n        #include <utility>\n\n        class Widget {\n        public:\n            Widget(int, double, const char*) {}\n        };\n\n        void test() {\n            auto ptr = std::make_unique<Widget>(42, 3.14, \"test\");\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_41(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        template<typename T1, typename T2>\n        void wrapper(T1&& arg1, T2&& arg2) {\n            process(std::forward<T1>(arg1), std::forward<T2>(arg2));\n        }\n\n        void process(int&, double&&) {}\n\n        void test() {\n            int x = 42;\n            wrapper(x, 3.14);\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_42(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        template<typename Func, typename T>\n        void apply(Func&& f, T&& arg) {\n            auto lambda = [&f](auto&& x) {\n                return std::forward<Func>(f)(std::forward<decltype(x)>(x));\n            };\n            lambda(std::forward<T>(arg));\n        }\n    ";

}

int TEST_F_MoveSemanticTestFixture_int_43(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        class Widget {\n        public:\n            Widget(Widget&&) = default;\n        };\n\n        void test() {\n            Widget w1;\n            Widget w2 = std::move(w1);\n            // w1 is now in a valid but unspecified state\n            Widget w3 = std::move(w1);  // Moving from moved-from object\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_44(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        #include <utility>\n\n        class Widget {\n            int* data;\n        public:\n            Widget& operator=(Widget&& other) noexcept {\n                if (this != &other) {  // Critical: check for self-assignment\n                    delete data;\n                    data = other.data;\n                    other.data = nullptr;\n                }\n                return *this;\n            }\n        };\n\n        void test() {\n            Widget w;\n            w = std::move(w);  // Self-move assignment\n        }\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_45(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n        public:\n            Widget(Widget&&) noexcept = default;\n            Widget& operator=(Widget&&) noexcept = default;\n        };\n\n        static_assert(noexcept(Widget(std::declval<Widget>())),\n                     \"Move constructor should be noexcept\");\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_46(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int* data;\n        public:\n            Widget(Widget&& other)  // Not noexcept\n                : data(new int(*other.data)) {  // May throw\n                other.data = nullptr;\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_47(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            const int value;  // Const member prevents default move\n        public:\n            Widget(Widget&& other) : value(other.value) {\n                // Const members are copied, not moved\n            }\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

int TEST_F_MoveSemanticTestFixture_int_48(struct MoveSemanticTestFixture, int) {
	const char *code = "\n        class Widget {\n            int& ref;  // Reference member prevents default move assignment\n        public:\n            Widget(int& r) : ref(r) {}\n            Widget(Widget&& other) : ref(other.ref) {}\n            // Move assignment would be implicitly deleted\n        };\n    ";

	struct MoveSemanticsFinder finder;

}

