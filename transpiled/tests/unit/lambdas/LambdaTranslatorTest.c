// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/lambdas/LambdaTranslatorTest.cpp
// Implementation file

#include "LambdaTranslatorTest.h"

static void LambdaTranslatorTest__ctor_default(struct LambdaTranslatorTest * this) {
}

static void LambdaTranslatorTest__ctor_copy(struct LambdaTranslatorTest * this, const struct LambdaTranslatorTest * other) {
}

int LambdaTranslatorTest_buildAST(struct LambdaTranslatorTest * this, const char * code) {
}

static void LambdaFinder__ctor_default(struct LambdaFinder * this) {
	this->lambdas = 0;
}

static void LambdaFinder__ctor_copy(struct LambdaFinder * this, const struct LambdaFinder * other) {
	this->lambdas = other->lambdas;
}

bool LambdaFinder_VisitLambdaExpr(struct LambdaFinder * this, int * E) {
	return true;
;
}

int * LambdaTranslatorTest_findFirstLambda(struct LambdaTranslatorTest * this, int * AST) {
	struct LambdaFinder finder;

}

int LambdaTranslatorTest_findAllLambdas(struct LambdaTranslatorTest * this, int * AST) {
	struct LambdaFinder finder;

}

int TEST_F(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() { return 42; };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() -> int { return 42; };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_1(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = [](int x, int y) { return x + y; };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_2(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 0;\n            auto lambda = [x]() mutable { x++; };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_3(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 0;\n            auto lambda = [&x]() { x = 42; };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_4(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = [](int x) {\n                int y = x * 2;\n                int z = y + 1;\n                return z;\n            };\n        }\n    ";

	int *lambda;

	const int *callOp;

	const int *body;

}

int TEST_F_LambdaTranslatorTest_int_5(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = [](int x, int y) -> double {\n                return static_cast<double>(x) / y;\n            };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_6(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int result = []() { return 42; }();\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_7(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() noexcept { return 42; };\n        }\n    ";

	int *lambda;

	const int *callOp;

	const int *FPT;

}

int TEST_F_LambdaTranslatorTest_int_8(struct LambdaTranslatorTest, int) {
	const char *code = "\n        template<typename... Args>\n        void foo() {\n            auto lambda = [](auto... args) { return sizeof...(args); };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_9(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 42;\n            auto lambda = [x]() { return x; };\n        }\n    ";

	int *lambda;

	const int &capture;

}

int TEST_F_LambdaTranslatorTest_int_10(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2, z = 3;\n            auto lambda = [x, y, z]() { return x + y + z; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_11(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 42;\n            auto lambda = [&x]() { x = 100; };\n        }\n    ";

	int *lambda;

	const int &capture;

}

int TEST_F_LambdaTranslatorTest_int_12(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2, z = 3;\n            auto lambda = [&x, &y, &z]() { x = y = z = 0; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_13(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2;\n            auto lambda = [=]() { return x + y; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_14(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2;\n            auto lambda = [&]() { x = y = 0; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_15(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2;\n            auto lambda = [x, &y]() { y = x; };\n        }\n    ";

	int *lambda;

	bool hasValue = false, hasRef = false;

}

int TEST_F_LambdaTranslatorTest_int_16(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = [x = 42]() { return x; };\n        }\n    ";

	int *lambda;

	const int &capture;

}

int TEST_F_LambdaTranslatorTest_int_17(struct LambdaTranslatorTest, int) {
	const char *code = "\n        class Foo {\n            int x;\n            void bar() {\n                auto lambda = [this]() { return x; };\n            }\n        };\n    ";

	int *lambda;

	const int &capture;

}

int TEST_F_LambdaTranslatorTest_int_18(struct LambdaTranslatorTest, int) {
	const char *code = "\n        class Foo {\n            int x;\n            void bar() {\n                auto lambda = [*this]() { return x; };\n            }\n        };\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_19(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2;\n            auto lambda = [=, &y]() { y = x; };\n        }\n    ";

	int *lambda;

	unsigned int explicitCaptures = 0;

}

int TEST_F_LambdaTranslatorTest_int_20(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            const int x = 42;\n            auto lambda = [x]() { return x; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_21(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1;\n            auto outer = [x]() {\n                auto inner = [x]() { return x; };\n                return inner();\n            };\n        }\n    ";

}

int TEST_F_LambdaTranslatorTest_int_22(struct LambdaTranslatorTest, int) {
	const char *code = "\n        #include <tuple>\n        void foo() {\n            auto [a, b] = std::make_tuple(1, 2);\n            auto lambda = [a, b]() { return a + b; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_23(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1;\n            {\n                int y = 2;\n                auto lambda = [x, y]() { return x + y; };\n            }\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_24(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2;\n            auto lambda = [x, y]() { return x + y; };\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_25(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2;\n            auto lambda = [x, y]() { return x + y; };\n        }\n    ";

	int *lambda;

	const int *closureType;

	unsigned int fieldCount = 0;

}

int TEST_F_LambdaTranslatorTest_int_26(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() { return 42; };\n            int (*fptr)() = lambda;\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_27(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1;\n            auto lambda = [x](int y) { return x + y; };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_28(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 42;\n            {\n                auto lambda = [x]() { return x; };\n                int result = lambda();\n            }\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_29(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1;\n            auto lambda = [&x]() { x++; };\n        }\n    ";

	int *lambda;

	const int *closureType;

	bool hasReferenceMember = false;

}

int TEST_F_LambdaTranslatorTest_int_30(struct LambdaTranslatorTest, int) {
	const char *code = "\n        class Foo {\n            int member;\n            void method() {\n                auto lambda = [this]() { return member; };\n            }\n        };\n    ";

	int *lambda;

	const int &capture;

}

int TEST_F_LambdaTranslatorTest_int_31(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() { return 42; };\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_32(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 42;\n            auto lambda1 = [x]() { return x; };\n            auto lambda2 = lambda1;\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_33(struct LambdaTranslatorTest, int) {
	const char *code = "\n        #include <utility>\n        void foo() {\n            int x = 42;\n            auto lambda1 = [x]() { return x; };\n            auto lambda2 = std::move(lambda1);\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_34(struct LambdaTranslatorTest, int) {
	const char *code = "\n        #include <string>\n        #include <vector>\n        void foo() {\n            std::string str = \"hello\";\n            std::vector<int> vec = {1, 2, 3};\n            auto lambda = [str, vec]() { return str.size() + vec.size(); };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_35(struct LambdaTranslatorTest, int) {
	const char *code = "\n        #include <string>\n        void foo() {\n            std::string str = \"hello\";\n            auto lambda = [str]() { return str; };\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_36(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() { return 42; };\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_37(struct LambdaTranslatorTest, int) {
	const char *code = "\n        template<typename F>\n        void apply(F func) { func(); }\n\n        void foo() {\n            apply([]() { return 42; });\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_38(struct LambdaTranslatorTest, int) {
	const char *code = "\n        auto make_lambda() {\n            return []() { return 42; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_39(struct LambdaTranslatorTest, int) {
	const char *code = "\n        #include <functional>\n        void foo() {\n            std::function<int()> func = []() { return 42; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_40(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = [](auto x) { return x + 1; };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_41(struct LambdaTranslatorTest, int) {
	const char *code = "\n        #include <vector>\n        #include <functional>\n        void foo() {\n            std::vector<std::function<int()>> funcs;\n            funcs.push_back([]() { return 42; });\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_42(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() { return 42; };\n            decltype(lambda) lambda2 = lambda;\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_43(struct LambdaTranslatorTest, int) {
	const char *code = "\n        template<typename T>\n        void apply(T value) {\n            auto lambda = [value]() { return value; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_44(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = [](int x) {\n                if (x > 0) return 42;\n                return -1;\n            };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_45(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = [](int x, int y) { return x + y; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_46(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() {};\n        }\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_47(struct LambdaTranslatorTest, int) {
	const char *code = "\n        #include <functional>\n        void foo() {\n            std::function<int(int)> fib = [&fib](int n) {\n                return n < 2 ? n : fib(n-1) + fib(n-2);\n            };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_48(struct LambdaTranslatorTest, int) {
	const char *code = "\n        constexpr auto lambda = []() { return 42; };\n        constexpr int value = lambda();\n    ";

	int *lambda;

	const int *callOp;

}

int TEST_F_LambdaTranslatorTest_int_49(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() noexcept(true) { return 42; };\n        }\n    ";

	int *lambda;

	const int *callOp;

	const int *FPT;

}

int TEST_F_LambdaTranslatorTest_int_50(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            decltype([]() { return 42; }) lambda;\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_51(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = []() [[nodiscard]] { return 42; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_52(struct LambdaTranslatorTest, int) {
	const char *code = "\n        template<typename F>\n        struct Wrapper { F func; };\n\n        void foo() {\n            Wrapper<decltype([](){ return 42; })> w;\n        }\n    ";

	int *lambda;

	const int *closureType;

}

int TEST_F_LambdaTranslatorTest_int_53(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto result = [](int x) { return x * 2; }(\n                          [](int y) { return y + 1; }(5));\n        }\n    ";

}

int TEST_F_LambdaTranslatorTest_int_54(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            int x = 1, y = 2;\n            auto lambda = [x, y,]() { return x + y; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_55(struct LambdaTranslatorTest, int) {
	const char *code = "\n        struct Foo {\n            int member;\n            void method() {\n                int local = 1;\n                auto lambda = [=, this]() { return member + local; };\n            }\n        };\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_56(struct LambdaTranslatorTest, int) {
	const char *code = "\n        #include <memory>\n        void foo() {\n            auto ptr = std::make_unique<int>(42);\n            auto lambda = [p = std::move(ptr)]() { return *p; };\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_57(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            if (auto lambda = []() { return 42; }; lambda() > 0) {\n                // use lambda\n            }\n        }\n    ";

	int *lambda;

}

int TEST_F_LambdaTranslatorTest_int_58(struct LambdaTranslatorTest, int) {
	const char *code = "\n        void foo() {\n            auto lambda = [](auto... args) {\n                return (args + ...);\n            };\n        }\n    ";

	int *lambda;

	const int *callOp;

}

