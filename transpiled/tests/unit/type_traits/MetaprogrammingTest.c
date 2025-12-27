// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/type_traits/MetaprogrammingTest.cpp
// Implementation file

#include "MetaprogrammingTest.h"

static void MetaprogrammingTest__ctor_default(struct MetaprogrammingTest * this) {
}

static void MetaprogrammingTest__ctor_copy(struct MetaprogrammingTest * this, const struct MetaprogrammingTest * other) {
}

int MetaprogrammingTest_buildAST(struct MetaprogrammingTest * this, const char * code) {
}

int TEST_F(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        struct TypeList {\n            static constexpr size_t size = sizeof...(Args);\n        };\n\n        void test() {\n            static_assert(TypeList<>::size == 0, \"empty type list\");\n            static_assert(TypeList<int>::size == 1, \"single type\");\n            static_assert(TypeList<int, double, char>::size == 3, \"three types\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        constexpr size_t count_args(Args... args) {\n            return sizeof...(args);\n        }\n\n        void test() {\n            static_assert(count_args() == 0, \"zero args\");\n            static_assert(count_args(1) == 1, \"one arg\");\n            static_assert(count_args(1, 2.0, 'c') == 3, \"three args\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_1(struct MetaprogrammingTest, int) {
	const char *code = "\n        void sink(int) {}\n\n        template<typename... Args>\n        void expand_and_call(Args... args) {\n            int dummy[] = { (sink(args), 0)... };\n            (void)dummy;\n        }\n\n        void test() {\n            expand_and_call(1, 2, 3);\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_2(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename T>\n        T identity(T value) {\n            return value;\n        }\n\n        template<typename... Args>\n        void forward_all(Args&&... args) {\n            int dummy[] = { identity(args)... };\n            (void)dummy;\n        }\n\n        void test() {\n            forward_all(1, 2, 3);\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_3(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Types>\n        struct TypeCount {\n            static constexpr size_t value = sizeof...(Types);\n        };\n\n        template<int... Values>\n        struct ValueCount {\n            static constexpr size_t value = sizeof...(Values);\n        };\n\n        void test() {\n            static_assert(TypeCount<int, double>::value == 2, \"two types\");\n            static_assert(ValueCount<1, 2, 3>::value == 3, \"three values\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_4(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename T>\n        struct Base {\n            T value;\n        };\n\n        template<typename... Bases>\n        struct Derived : public Bases... {\n        };\n\n        void test() {\n            Derived<Base<int>, Base<double>> d;\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_5(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        auto make_tuple(Args... args) {\n            return [args...] { return sizeof...(args); };\n        }\n\n        void test() {\n            auto t = make_tuple(1, 2, 3);\n            int size = t();\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_6(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<int... Values>\n        struct IntList {\n            static constexpr int sum() {\n                return (Values + ... + 0);\n            }\n        };\n\n        void test() {\n            static_assert(IntList<1, 2, 3>::sum() == 6, \"sum is 6\");\n            static_assert(IntList<>::sum() == 0, \"empty sum is 0\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_7(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        struct Container {\n            static constexpr bool empty = (sizeof...(Args) == 0);\n        };\n\n        void test() {\n            static_assert(Container<>::empty, \"empty container\");\n            static_assert(!Container<int>::empty, \"non-empty container\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_8(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename First, typename... Rest>\n        struct TypeList {\n            using first_type = First;\n            static constexpr size_t rest_count = sizeof...(Rest);\n        };\n\n        void test() {\n            using List = TypeList<int, double, char>;\n            static_assert(List::rest_count == 2, \"two remaining types\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_9(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<int N>\n        struct Factorial {\n            static constexpr int value = N * Factorial<N - 1>::value;\n        };\n\n        template<>\n        struct Factorial<0> {\n            static constexpr int value = 1;\n        };\n\n        void test() {\n            static_assert(Factorial<5>::value == 120, \"5! = 120\");\n            static_assert(Factorial<0>::value == 1, \"0! = 1\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_10(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<int N>\n        struct Fibonacci {\n            static constexpr int value = Fibonacci<N-1>::value + Fibonacci<N-2>::value;\n        };\n\n        template<>\n        struct Fibonacci<0> {\n            static constexpr int value = 0;\n        };\n\n        template<>\n        struct Fibonacci<1> {\n            static constexpr int value = 1;\n        };\n\n        void test() {\n            static_assert(Fibonacci<6>::value == 8, \"fib(6) = 8\");\n            static_assert(Fibonacci<0>::value == 0, \"fib(0) = 0\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_11(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Types>\n        struct TypeListSize;\n\n        template<>\n        struct TypeListSize<> {\n            static constexpr size_t value = 0;\n        };\n\n        template<typename First, typename... Rest>\n        struct TypeListSize<First, Rest...> {\n            static constexpr size_t value = 1 + TypeListSize<Rest...>::value;\n        };\n\n        void test() {\n            static_assert(TypeListSize<int, double, char>::value == 3, \"three types\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_12(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<int A, int B>\n        struct Max {\n            static constexpr int value = (A > B) ? A : B;\n        };\n\n        template<int First, int... Rest>\n        struct MaxOf {\n            static constexpr int value = Max<First, MaxOf<Rest...>::value>::value;\n        };\n\n        template<int Last>\n        struct MaxOf<Last> {\n            static constexpr int value = Last;\n        };\n\n        void test() {\n            static_assert(MaxOf<5, 2, 8, 1>::value == 8, \"max is 8\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_13(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<int Base, int Exp>\n        struct Power {\n            static constexpr int value = Base * Power<Base, Exp - 1>::value;\n        };\n\n        template<int Base>\n        struct Power<Base, 0> {\n            static constexpr int value = 1;\n        };\n\n        void test() {\n            static_assert(Power<2, 10>::value == 1024, \"2^10 = 1024\");\n            static_assert(Power<3, 3>::value == 27, \"3^3 = 27\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_14(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<int A, int B>\n        struct GCD {\n            static constexpr int value = GCD<B, A % B>::value;\n        };\n\n        template<int A>\n        struct GCD<A, 0> {\n            static constexpr int value = A;\n        };\n\n        void test() {\n            static_assert(GCD<48, 18>::value == 6, \"gcd(48, 18) = 6\");\n            static_assert(GCD<100, 50>::value == 50, \"gcd(100, 50) = 50\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_15(struct MetaprogrammingTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename... Types>\n        struct TypeList {};\n\n        template<typename List, typename... Accumulated>\n        struct ReverseImpl;\n\n        template<typename... Accumulated>\n        struct ReverseImpl<TypeList<>, Accumulated...> {\n            using type = TypeList<Accumulated...>;\n        };\n\n        template<typename First, typename... Rest, typename... Accumulated>\n        struct ReverseImpl<TypeList<First, Rest...>, Accumulated...> {\n            using type = typename ReverseImpl<TypeList<Rest...>, First, Accumulated...>::type;\n        };\n\n        template<typename List>\n        using Reverse = typename ReverseImpl<List>::type;\n\n        void test() {\n            using Original = TypeList<int, double, char>;\n            using Reversed = Reverse<Original>;\n            // Validation would require more complex type checking\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_16(struct MetaprogrammingTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T, typename... List>\n        struct Contains;\n\n        template<typename T>\n        struct Contains<T> {\n            static constexpr bool value = false;\n        };\n\n        template<typename T, typename First, typename... Rest>\n        struct Contains<T, First, Rest...> {\n            static constexpr bool value =\n                std::is_same<T, First>::value || Contains<T, Rest...>::value;\n        };\n\n        void test() {\n            static_assert(Contains<int, int, double, char>::value, \"contains int\");\n            static_assert(!Contains<float, int, double, char>::value, \"doesn't contain float\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_17(struct MetaprogrammingTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T, typename... List>\n        struct IndexOf;\n\n        template<typename T, typename First, typename... Rest>\n        struct IndexOf<T, First, Rest...> {\n            static constexpr int value =\n                std::is_same<T, First>::value ? 0 : 1 + IndexOf<T, Rest...>::value;\n        };\n\n        template<typename T>\n        struct IndexOf<T> {\n            static constexpr int value = -1;\n        };\n\n        void test() {\n            static_assert(IndexOf<int, int, double, char>::value == 0, \"int at index 0\");\n            static_assert(IndexOf<char, int, double, char>::value == 2, \"char at index 2\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_18(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<int N>\n        struct Outer {\n            template<int M>\n            struct Inner {\n                static constexpr int value = N * M;\n            };\n        };\n\n        template<int N, int M>\n        struct Multiply {\n            static constexpr int value = Outer<N>::template Inner<M>::value;\n        };\n\n        void test() {\n            static_assert(Multiply<5, 6>::value == 30, \"5 * 6 = 30\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_19(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr int square(int x) {\n            return x * x;\n        }\n\n        void test() {\n            static_assert(square(5) == 25, \"5^2 = 25\");\n            constexpr int result = square(10);\n            static_assert(result == 100, \"10^2 = 100\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_20(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr int abs(int x) {\n            return x < 0 ? -x : x;\n        }\n\n        void test() {\n            static_assert(abs(-5) == 5, \"abs(-5) = 5\");\n            static_assert(abs(5) == 5, \"abs(5) = 5\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_21(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr int factorial(int n) {\n            return n <= 1 ? 1 : n * factorial(n - 1);\n        }\n\n        void test() {\n            static_assert(factorial(5) == 120, \"5! = 120\");\n            static_assert(factorial(0) == 1, \"0! = 1\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_22(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr int sum_range(int n) {\n            int result = 0;\n            for (int i = 1; i <= n; ++i) {\n                result += i;\n            }\n            return result;\n        }\n\n        void test() {\n            static_assert(sum_range(10) == 55, \"sum(1..10) = 55\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_23(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr int classify(int x) {\n            if (x < 0) return -1;\n            if (x > 0) return 1;\n            return 0;\n        }\n\n        void test() {\n            static_assert(classify(-5) == -1, \"negative\");\n            static_assert(classify(5) == 1, \"positive\");\n            static_assert(classify(0) == 0, \"zero\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_24(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename T>\n        constexpr T max(T a, T b) {\n            return a > b ? a : b;\n        }\n\n        void test() {\n            static_assert(max(5, 10) == 10, \"max(5, 10) = 10\");\n            static_assert(max(3.14, 2.71) == 3.14, \"max doubles\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_25(struct MetaprogrammingTest, int) {
	const char *code = "\n        struct Point {\n            int x, y;\n            constexpr Point(int x_, int y_) : x(x_), y(y_) {}\n            constexpr int distanceSquared() const {\n                return x * x + y * y;\n            }\n        };\n\n        void test() {\n            constexpr Point p(3, 4);\n            static_assert(p.distanceSquared() == 25, \"3^2 + 4^2 = 25\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_26(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr int sum_array(const int* arr, int size) {\n            int sum = 0;\n            for (int i = 0; i < size; ++i) {\n                sum += arr[i];\n            }\n            return sum;\n        }\n\n        void test() {\n            constexpr int arr[] = {1, 2, 3, 4, 5};\n            static_assert(sum_array(arr, 5) == 15, \"sum = 15\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_27(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr int string_length(const char* str) {\n            int len = 0;\n            while (str[len] != '\\0') {\n                ++len;\n            }\n            return len;\n        }\n\n        void test() {\n            static_assert(string_length(\"hello\") == 5, \"length of 'hello' is 5\");\n            static_assert(string_length(\"\") == 0, \"empty string length is 0\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_28(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr bool is_prime(int n) {\n            if (n <= 1) return false;\n            if (n <= 3) return true;\n            if (n % 2 == 0 || n % 3 == 0) return false;\n            for (int i = 5; i * i <= n; i += 6) {\n                if (n % i == 0 || n % (i + 2) == 0)\n                    return false;\n            }\n            return true;\n        }\n\n        void test() {\n            static_assert(is_prime(7), \"7 is prime\");\n            static_assert(!is_prime(8), \"8 is not prime\");\n            static_assert(is_prime(13), \"13 is prime\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_29(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        constexpr auto sum(Args... args) {\n            return (... + args);\n        }\n\n        void test() {\n            static_assert(sum(1, 2, 3, 4) == 10, \"sum = 10\");\n            static_assert(sum(5) == 5, \"single element\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_30(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        constexpr auto multiply(Args... args) {\n            return (args * ...);\n        }\n\n        void test() {\n            static_assert(multiply(2, 3, 4) == 24, \"product = 24\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_31(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        constexpr auto sum_with_init(Args... args) {\n            return (0 + ... + args);\n        }\n\n        void test() {\n            static_assert(sum_with_init(1, 2, 3) == 6, \"sum with init = 6\");\n            static_assert(sum_with_init() == 0, \"empty sum = 0\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_32(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        constexpr bool all_true(Args... args) {\n            return (... && args);\n        }\n\n        void test() {\n            static_assert(all_true(true, true, true), \"all true\");\n            static_assert(!all_true(true, false, true), \"contains false\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_33(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Args>\n        constexpr bool any_true(Args... args) {\n            return (... || args);\n        }\n\n        void test() {\n            static_assert(any_true(false, true, false), \"contains true\");\n            static_assert(!any_true(false, false, false), \"all false\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_34(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr int twice(int x) { return x * 2; }\n\n        template<typename... Args>\n        constexpr int sum_doubled(Args... args) {\n            return (... + twice(args));\n        }\n\n        void test() {\n            static_assert(sum_doubled(1, 2, 3) == 12, \"sum of doubled = 12\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_35(struct MetaprogrammingTest, int) {
	const char *code = "\n        #include <utility>\n\n        template<typename... Args>\n        void forward_to_sink(Args&&... args) {\n            int dummy[] = { (static_cast<void>(std::forward<Args>(args)), 0)... };\n            (void)dummy;\n        }\n\n        void test() {\n            int x = 5;\n            forward_to_sink(x, 10, 15);\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_36(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename T>\n        struct Wrapper {\n            T value;\n        };\n\n        template<template<typename> class Container, typename T>\n        struct Apply {\n            using type = Container<T>;\n        };\n\n        void test() {\n            using Result = Apply<Wrapper, int>::type;\n            Result r;\n            r.value = 42;\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_37(struct MetaprogrammingTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr int dispatch() {\n            if constexpr (std::is_integral<T>::value) {\n                return 1;\n            } else if constexpr (std::is_floating_point<T>::value) {\n                return 2;\n            } else {\n                return 0;\n            }\n        }\n\n        void test() {\n            static_assert(dispatch<int>() == 1, \"integral dispatch\");\n            static_assert(dispatch<double>() == 2, \"floating dispatch\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_38(struct MetaprogrammingTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr auto get_value(T x) {\n            if constexpr (std::is_pointer<T>::value) {\n                return *x;\n            } else {\n                return x;\n            }\n        }\n\n        void test() {\n            constexpr int x = 42;\n            constexpr int* px = &x;\n            static_assert(get_value(x) == 42, \"direct value\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_39(struct MetaprogrammingTest, int) {
	const char *code = "\n        constexpr unsigned int hash(const char* str) {\n            unsigned int h = 5381;\n            while (*str) {\n                h = ((h << 5) + h) + static_cast<unsigned int>(*str++);\n            }\n            return h;\n        }\n\n        void test() {\n            constexpr unsigned int h1 = hash(\"hello\");\n            constexpr unsigned int h2 = hash(\"world\");\n            static_assert(h1 != h2, \"different hashes\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_40(struct MetaprogrammingTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename... Types>\n        struct AllIntegral {\n            static constexpr bool value = (std::is_integral<Types>::value && ...);\n        };\n\n        void test() {\n            static_assert(AllIntegral<int, long, short>::value, \"all integral\");\n            static_assert(!AllIntegral<int, double, long>::value, \"not all integral\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_41(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename T>\n        constexpr T min(T a, T b) {\n            return a < b ? a : b;\n        }\n\n        template<typename T, typename... Rest>\n        constexpr T min(T first, Rest... rest) {\n            return min(first, min(rest...));\n        }\n\n        void test() {\n            static_assert(min(5, 2, 8, 1, 9) == 1, \"min is 1\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_42(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<size_t Index, typename... Types>\n        struct TypeAt;\n\n        template<typename First, typename... Rest>\n        struct TypeAt<0, First, Rest...> {\n            using type = First;\n        };\n\n        template<size_t Index, typename First, typename... Rest>\n        struct TypeAt<Index, First, Rest...> {\n            using type = typename TypeAt<Index - 1, Rest...>::type;\n        };\n\n        void test() {\n            using Types = TypeAt<0, int, double, char>;\n            static_assert(sizeof(typename Types::type) == sizeof(int), \"first type is int\");\n        }\n    ";

	auto AST;

}

int TEST_F_MetaprogrammingTest_int_43(struct MetaprogrammingTest, int) {
	const char *code = "\n        template<typename... Ts>\n        struct TypeList {};\n\n        template<typename T1, typename T2>\n        struct Pair {};\n\n        template<typename List1, typename List2>\n        struct CartesianProduct;\n\n        template<typename... T1s, typename... T2s>\n        struct CartesianProduct<TypeList<T1s...>, TypeList<T2s...>> {\n            static constexpr size_t size = sizeof...(T1s) * sizeof...(T2s);\n        };\n\n        void test() {\n            using L1 = TypeList<int, double>;\n            using L2 = TypeList<char, float, long>;\n            static_assert(CartesianProduct<L1, L2>::size == 6, \"2 * 3 = 6\");\n        }\n    ";

	auto AST;

}

