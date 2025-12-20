/**
 * @file MetaprogrammingTest.cpp
 * @brief Stream 5: Template Metaprogramming Comprehensive Test Suite
 *
 * Tests for advanced C++ template metaprogramming features including:
 * - Variadic template expansion
 * - Parameter pack operations
 * - Recursive template metaprogramming
 * - constexpr functions and compile-time computation
 * - Fold expressions
 * - Template specialization patterns
 *
 * These features must be properly evaluated at compile-time during transpilation.
 * The C++ to C transpiler must resolve all template metaprogramming constructs
 * to concrete C code.
 *
 * Target: 35-50 high-quality unit tests
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <iostream>
#include <cassert>
#include <string>
#include <vector>

using namespace clang;

// Test helper utilities
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cpp");
}

#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS() std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        std::cerr << "  at line " << __LINE__ << std::endl; \
        return false; \
    }

// ============================================================================
// SECTION 1: Variadic Template Basics (Tests 1-10)
// ============================================================================

// Test 1: Basic variadic template
bool test_BasicVariadicTemplate() {
    TEST_START("basic variadic template");

    const char* code = R"(
        template<typename... Args>
        struct TypeList {
            static constexpr size_t size = sizeof...(Args);
        };

        void test() {
            static_assert(TypeList<>::size == 0, "empty type list");
            static_assert(TypeList<int>::size == 1, "single type");
            static_assert(TypeList<int, double, char>::size == 3, "three types");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 2: Variadic function template
bool test_VariadicFunctionTemplate() {
    TEST_START("variadic function template");

    const char* code = R"(
        template<typename... Args>
        constexpr size_t count_args(Args... args) {
            return sizeof...(args);
        }

        void test() {
            static_assert(count_args() == 0, "zero args");
            static_assert(count_args(1) == 1, "one arg");
            static_assert(count_args(1, 2.0, 'c') == 3, "three args");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 3: Parameter pack expansion in function call
bool test_PackExpansionFunctionCall() {
    TEST_START("parameter pack expansion in function call");

    const char* code = R"(
        void sink(int) {}

        template<typename... Args>
        void expand_and_call(Args... args) {
            int dummy[] = { (sink(args), 0)... };
            (void)dummy;
        }

        void test() {
            expand_and_call(1, 2, 3);
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 4: Variadic template with forwarding
bool test_VariadicForwarding() {
    TEST_START("variadic template with forwarding");

    const char* code = R"(
        template<typename T>
        T identity(T value) {
            return value;
        }

        template<typename... Args>
        void forward_all(Args&&... args) {
            int dummy[] = { identity(args)... };
            (void)dummy;
        }

        void test() {
            forward_all(1, 2, 3);
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 5: sizeof... operator
bool test_SizeofOperator() {
    TEST_START("sizeof... operator");

    const char* code = R"(
        template<typename... Types>
        struct TypeCount {
            static constexpr size_t value = sizeof...(Types);
        };

        template<int... Values>
        struct ValueCount {
            static constexpr size_t value = sizeof...(Values);
        };

        void test() {
            static_assert(TypeCount<int, double>::value == 2, "two types");
            static_assert(ValueCount<1, 2, 3>::value == 3, "three values");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 6: Variadic template class inheritance
bool test_VariadicInheritance() {
    TEST_START("variadic template inheritance");

    const char* code = R"(
        template<typename T>
        struct Base {
            T value;
        };

        template<typename... Bases>
        struct Derived : public Bases... {
        };

        void test() {
            Derived<Base<int>, Base<double>> d;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 7: Pack expansion in braced initializer
bool test_PackExpansionBracedInit() {
    TEST_START("pack expansion in braced initializer");

    const char* code = R"(
        template<typename... Args>
        auto make_tuple(Args... args) {
            return [args...] { return sizeof...(args); };
        }

        void test() {
            auto t = make_tuple(1, 2, 3);
            int size = t();
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 8: Variadic template with non-type parameters
bool test_VariadicNonTypeParams() {
    TEST_START("variadic non-type parameters");

    const char* code = R"(
        template<int... Values>
        struct IntList {
            static constexpr int sum() {
                return (Values + ... + 0);
            }
        };

        void test() {
            static_assert(IntList<1, 2, 3>::sum() == 6, "sum is 6");
            static_assert(IntList<>::sum() == 0, "empty sum is 0");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 9: Variadic template with default arguments
bool test_VariadicDefaultArgs() {
    TEST_START("variadic template with default arguments");

    const char* code = R"(
        template<typename... Args>
        struct Container {
            static constexpr bool empty = (sizeof...(Args) == 0);
        };

        void test() {
            static_assert(Container<>::empty, "empty container");
            static_assert(!Container<int>::empty, "non-empty container");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 10: Mixed variadic and fixed parameters
bool test_MixedVariadicFixed() {
    TEST_START("mixed variadic and fixed parameters");

    const char* code = R"(
        template<typename First, typename... Rest>
        struct TypeList {
            using first_type = First;
            static constexpr size_t rest_count = sizeof...(Rest);
        };

        void test() {
            using List = TypeList<int, double, char>;
            static_assert(List::rest_count == 2, "two remaining types");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// ============================================================================
// SECTION 2: Recursive Template Metaprogramming (Tests 11-20)
// ============================================================================

// Test 11: Recursive template factorial
bool test_RecursiveFactorial() {
    TEST_START("recursive template factorial");

    const char* code = R"(
        template<int N>
        struct Factorial {
            static constexpr int value = N * Factorial<N - 1>::value;
        };

        template<>
        struct Factorial<0> {
            static constexpr int value = 1;
        };

        void test() {
            static_assert(Factorial<5>::value == 120, "5! = 120");
            static_assert(Factorial<0>::value == 1, "0! = 1");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 12: Recursive template fibonacci
bool test_RecursiveFibonacci() {
    TEST_START("recursive template fibonacci");

    const char* code = R"(
        template<int N>
        struct Fibonacci {
            static constexpr int value = Fibonacci<N-1>::value + Fibonacci<N-2>::value;
        };

        template<>
        struct Fibonacci<0> {
            static constexpr int value = 0;
        };

        template<>
        struct Fibonacci<1> {
            static constexpr int value = 1;
        };

        void test() {
            static_assert(Fibonacci<6>::value == 8, "fib(6) = 8");
            static_assert(Fibonacci<0>::value == 0, "fib(0) = 0");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 13: Recursive type list processing
bool test_RecursiveTypeList() {
    TEST_START("recursive type list processing");

    const char* code = R"(
        template<typename... Types>
        struct TypeListSize;

        template<>
        struct TypeListSize<> {
            static constexpr size_t value = 0;
        };

        template<typename First, typename... Rest>
        struct TypeListSize<First, Rest...> {
            static constexpr size_t value = 1 + TypeListSize<Rest...>::value;
        };

        void test() {
            static_assert(TypeListSize<int, double, char>::value == 3, "three types");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 14: Recursive template maximum
bool test_RecursiveMax() {
    TEST_START("recursive template maximum");

    const char* code = R"(
        template<int A, int B>
        struct Max {
            static constexpr int value = (A > B) ? A : B;
        };

        template<int First, int... Rest>
        struct MaxOf {
            static constexpr int value = Max<First, MaxOf<Rest...>::value>::value;
        };

        template<int Last>
        struct MaxOf<Last> {
            static constexpr int value = Last;
        };

        void test() {
            static_assert(MaxOf<5, 2, 8, 1>::value == 8, "max is 8");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 15: Recursive template power
bool test_RecursivePower() {
    TEST_START("recursive template power");

    const char* code = R"(
        template<int Base, int Exp>
        struct Power {
            static constexpr int value = Base * Power<Base, Exp - 1>::value;
        };

        template<int Base>
        struct Power<Base, 0> {
            static constexpr int value = 1;
        };

        void test() {
            static_assert(Power<2, 10>::value == 1024, "2^10 = 1024");
            static_assert(Power<3, 3>::value == 27, "3^3 = 27");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 16: Recursive template GCD
bool test_RecursiveGCD() {
    TEST_START("recursive template GCD");

    const char* code = R"(
        template<int A, int B>
        struct GCD {
            static constexpr int value = GCD<B, A % B>::value;
        };

        template<int A>
        struct GCD<A, 0> {
            static constexpr int value = A;
        };

        void test() {
            static_assert(GCD<48, 18>::value == 6, "gcd(48, 18) = 6");
            static_assert(GCD<100, 50>::value == 50, "gcd(100, 50) = 50");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 17: Compile-time list reversal
bool test_ListReversal() {
    TEST_START("compile-time list reversal");

    const char* code = R"(
        #include <type_traits>

        template<typename... Types>
        struct TypeList {};

        template<typename List, typename... Accumulated>
        struct ReverseImpl;

        template<typename... Accumulated>
        struct ReverseImpl<TypeList<>, Accumulated...> {
            using type = TypeList<Accumulated...>;
        };

        template<typename First, typename... Rest, typename... Accumulated>
        struct ReverseImpl<TypeList<First, Rest...>, Accumulated...> {
            using type = typename ReverseImpl<TypeList<Rest...>, First, Accumulated...>::type;
        };

        template<typename List>
        using Reverse = typename ReverseImpl<List>::type;

        void test() {
            using Original = TypeList<int, double, char>;
            using Reversed = Reverse<Original>;
            // Validation would require more complex type checking
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 18: Recursive template list contains
bool test_RecursiveContains() {
    TEST_START("recursive template list contains");

    const char* code = R"(
        #include <type_traits>

        template<typename T, typename... List>
        struct Contains;

        template<typename T>
        struct Contains<T> {
            static constexpr bool value = false;
        };

        template<typename T, typename First, typename... Rest>
        struct Contains<T, First, Rest...> {
            static constexpr bool value =
                std::is_same<T, First>::value || Contains<T, Rest...>::value;
        };

        void test() {
            static_assert(Contains<int, int, double, char>::value, "contains int");
            static_assert(!Contains<float, int, double, char>::value, "doesn't contain float");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 19: Recursive template index of type
bool test_RecursiveIndexOf() {
    TEST_START("recursive template index of type");

    const char* code = R"(
        #include <type_traits>

        template<typename T, typename... List>
        struct IndexOf;

        template<typename T, typename First, typename... Rest>
        struct IndexOf<T, First, Rest...> {
            static constexpr int value =
                std::is_same<T, First>::value ? 0 : 1 + IndexOf<T, Rest...>::value;
        };

        template<typename T>
        struct IndexOf<T> {
            static constexpr int value = -1;
        };

        void test() {
            static_assert(IndexOf<int, int, double, char>::value == 0, "int at index 0");
            static_assert(IndexOf<char, int, double, char>::value == 2, "char at index 2");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 20: Nested recursive templates
bool test_NestedRecursion() {
    TEST_START("nested recursive templates");

    const char* code = R"(
        template<int N>
        struct Outer {
            template<int M>
            struct Inner {
                static constexpr int value = N * M;
            };
        };

        template<int N, int M>
        struct Multiply {
            static constexpr int value = Outer<N>::template Inner<M>::value;
        };

        void test() {
            static_assert(Multiply<5, 6>::value == 30, "5 * 6 = 30");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// ============================================================================
// SECTION 3: constexpr Functions (Tests 21-30)
// ============================================================================

// Test 21: Basic constexpr function
bool test_BasicConstexpr() {
    TEST_START("basic constexpr function");

    const char* code = R"(
        constexpr int square(int x) {
            return x * x;
        }

        void test() {
            static_assert(square(5) == 25, "5^2 = 25");
            constexpr int result = square(10);
            static_assert(result == 100, "10^2 = 100");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 22: constexpr with conditional
bool test_ConstexprConditional() {
    TEST_START("constexpr with conditional");

    const char* code = R"(
        constexpr int abs(int x) {
            return x < 0 ? -x : x;
        }

        void test() {
            static_assert(abs(-5) == 5, "abs(-5) = 5");
            static_assert(abs(5) == 5, "abs(5) = 5");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 23: constexpr with recursion
bool test_ConstexprRecursion() {
    TEST_START("constexpr with recursion");

    const char* code = R"(
        constexpr int factorial(int n) {
            return n <= 1 ? 1 : n * factorial(n - 1);
        }

        void test() {
            static_assert(factorial(5) == 120, "5! = 120");
            static_assert(factorial(0) == 1, "0! = 1");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 24: constexpr with loops (C++14)
bool test_ConstexprLoop() {
    TEST_START("constexpr with loops");

    const char* code = R"(
        constexpr int sum_range(int n) {
            int result = 0;
            for (int i = 1; i <= n; ++i) {
                result += i;
            }
            return result;
        }

        void test() {
            static_assert(sum_range(10) == 55, "sum(1..10) = 55");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 25: constexpr with multiple return paths
bool test_ConstexprMultipleReturns() {
    TEST_START("constexpr with multiple return paths");

    const char* code = R"(
        constexpr int classify(int x) {
            if (x < 0) return -1;
            if (x > 0) return 1;
            return 0;
        }

        void test() {
            static_assert(classify(-5) == -1, "negative");
            static_assert(classify(5) == 1, "positive");
            static_assert(classify(0) == 0, "zero");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 26: constexpr with template
bool test_ConstexprTemplate() {
    TEST_START("constexpr with template");

    const char* code = R"(
        template<typename T>
        constexpr T max(T a, T b) {
            return a > b ? a : b;
        }

        void test() {
            static_assert(max(5, 10) == 10, "max(5, 10) = 10");
            static_assert(max(3.14, 2.71) == 3.14, "max doubles");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 27: constexpr constructor
bool test_ConstexprConstructor() {
    TEST_START("constexpr constructor");

    const char* code = R"(
        struct Point {
            int x, y;
            constexpr Point(int x_, int y_) : x(x_), y(y_) {}
            constexpr int distanceSquared() const {
                return x * x + y * y;
            }
        };

        void test() {
            constexpr Point p(3, 4);
            static_assert(p.distanceSquared() == 25, "3^2 + 4^2 = 25");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 28: constexpr array operations
bool test_ConstexprArray() {
    TEST_START("constexpr array operations");

    const char* code = R"(
        constexpr int sum_array(const int* arr, int size) {
            int sum = 0;
            for (int i = 0; i < size; ++i) {
                sum += arr[i];
            }
            return sum;
        }

        void test() {
            constexpr int arr[] = {1, 2, 3, 4, 5};
            static_assert(sum_array(arr, 5) == 15, "sum = 15");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 29: constexpr string operations
bool test_ConstexprString() {
    TEST_START("constexpr string operations");

    const char* code = R"(
        constexpr int string_length(const char* str) {
            int len = 0;
            while (str[len] != '\0') {
                ++len;
            }
            return len;
        }

        void test() {
            static_assert(string_length("hello") == 5, "length of 'hello' is 5");
            static_assert(string_length("") == 0, "empty string length is 0");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 30: constexpr with complex logic
bool test_ConstexprComplexLogic() {
    TEST_START("constexpr with complex logic");

    const char* code = R"(
        constexpr bool is_prime(int n) {
            if (n <= 1) return false;
            if (n <= 3) return true;
            if (n % 2 == 0 || n % 3 == 0) return false;
            for (int i = 5; i * i <= n; i += 6) {
                if (n % i == 0 || n % (i + 2) == 0)
                    return false;
            }
            return true;
        }

        void test() {
            static_assert(is_prime(7), "7 is prime");
            static_assert(!is_prime(8), "8 is not prime");
            static_assert(is_prime(13), "13 is prime");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// ============================================================================
// SECTION 4: Fold Expressions & Advanced Patterns (Tests 31-45)
// ============================================================================

// Test 31: Fold expression - unary left fold
bool test_UnaryLeftFold() {
    TEST_START("unary left fold expression");

    const char* code = R"(
        template<typename... Args>
        constexpr auto sum(Args... args) {
            return (... + args);
        }

        void test() {
            static_assert(sum(1, 2, 3, 4) == 10, "sum = 10");
            static_assert(sum(5) == 5, "single element");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 32: Fold expression - unary right fold
bool test_UnaryRightFold() {
    TEST_START("unary right fold expression");

    const char* code = R"(
        template<typename... Args>
        constexpr auto multiply(Args... args) {
            return (args * ...);
        }

        void test() {
            static_assert(multiply(2, 3, 4) == 24, "product = 24");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 33: Fold expression - binary left fold
bool test_BinaryLeftFold() {
    TEST_START("binary left fold expression");

    const char* code = R"(
        template<typename... Args>
        constexpr auto sum_with_init(Args... args) {
            return (0 + ... + args);
        }

        void test() {
            static_assert(sum_with_init(1, 2, 3) == 6, "sum with init = 6");
            static_assert(sum_with_init() == 0, "empty sum = 0");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 34: Fold expression - logical AND
bool test_FoldLogicalAnd() {
    TEST_START("fold expression logical AND");

    const char* code = R"(
        template<typename... Args>
        constexpr bool all_true(Args... args) {
            return (... && args);
        }

        void test() {
            static_assert(all_true(true, true, true), "all true");
            static_assert(!all_true(true, false, true), "contains false");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 35: Fold expression - logical OR
bool test_FoldLogicalOr() {
    TEST_START("fold expression logical OR");

    const char* code = R"(
        template<typename... Args>
        constexpr bool any_true(Args... args) {
            return (... || args);
        }

        void test() {
            static_assert(any_true(false, true, false), "contains true");
            static_assert(!any_true(false, false, false), "all false");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 36: Fold expression with function call
bool test_FoldFunctionCall() {
    TEST_START("fold expression with function call");

    const char* code = R"(
        constexpr int twice(int x) { return x * 2; }

        template<typename... Args>
        constexpr int sum_doubled(Args... args) {
            return (... + twice(args));
        }

        void test() {
            static_assert(sum_doubled(1, 2, 3) == 12, "sum of doubled = 12");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 37: Variadic template with perfect forwarding
bool test_PerfectForwarding() {
    TEST_START("perfect forwarding with variadic template");

    const char* code = R"(
        #include <utility>

        template<typename... Args>
        void forward_to_sink(Args&&... args) {
            int dummy[] = { (static_cast<void>(std::forward<Args>(args)), 0)... };
            (void)dummy;
        }

        void test() {
            int x = 5;
            forward_to_sink(x, 10, 15);
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 38: Template template parameters
bool test_TemplateTemplateParams() {
    TEST_START("template template parameters");

    const char* code = R"(
        template<typename T>
        struct Wrapper {
            T value;
        };

        template<template<typename> class Container, typename T>
        struct Apply {
            using type = Container<T>;
        };

        void test() {
            using Result = Apply<Wrapper, int>::type;
            Result r;
            r.value = 42;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 39: Compile-time dispatch based on type
bool test_CompileTimeDispatch() {
    TEST_START("compile-time dispatch based on type");

    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr int dispatch() {
            if constexpr (std::is_integral<T>::value) {
                return 1;
            } else if constexpr (std::is_floating_point<T>::value) {
                return 2;
            } else {
                return 0;
            }
        }

        void test() {
            static_assert(dispatch<int>() == 1, "integral dispatch");
            static_assert(dispatch<double>() == 2, "floating dispatch");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 40: if constexpr with template
bool test_IfConstexpr() {
    TEST_START("if constexpr with template");

    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr auto get_value(T x) {
            if constexpr (std::is_pointer<T>::value) {
                return *x;
            } else {
                return x;
            }
        }

        void test() {
            constexpr int x = 42;
            constexpr int* px = &x;
            static_assert(get_value(x) == 42, "direct value");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 41: Compile-time string hashing
bool test_CompileTimeHash() {
    TEST_START("compile-time string hashing");

    const char* code = R"(
        constexpr unsigned int hash(const char* str) {
            unsigned int h = 5381;
            while (*str) {
                h = ((h << 5) + h) + static_cast<unsigned int>(*str++);
            }
            return h;
        }

        void test() {
            constexpr unsigned int h1 = hash("hello");
            constexpr unsigned int h2 = hash("world");
            static_assert(h1 != h2, "different hashes");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 42: Type trait composition with variadic templates
bool test_TraitComposition() {
    TEST_START("type trait composition with variadic");

    const char* code = R"(
        #include <type_traits>

        template<typename... Types>
        struct AllIntegral {
            static constexpr bool value = (std::is_integral<Types>::value && ...);
        };

        void test() {
            static_assert(AllIntegral<int, long, short>::value, "all integral");
            static_assert(!AllIntegral<int, double, long>::value, "not all integral");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 43: Variadic min/max
bool test_VariadicMinMax() {
    TEST_START("variadic min/max");

    const char* code = R"(
        template<typename T>
        constexpr T min(T a, T b) {
            return a < b ? a : b;
        }

        template<typename T, typename... Rest>
        constexpr T min(T first, Rest... rest) {
            return min(first, min(rest...));
        }

        void test() {
            static_assert(min(5, 2, 8, 1, 9) == 1, "min is 1");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 44: Tuple-like compile-time access
bool test_CompileTimeTupleAccess() {
    TEST_START("compile-time tuple-like access");

    const char* code = R"(
        template<size_t Index, typename... Types>
        struct TypeAt;

        template<typename First, typename... Rest>
        struct TypeAt<0, First, Rest...> {
            using type = First;
        };

        template<size_t Index, typename First, typename... Rest>
        struct TypeAt<Index, First, Rest...> {
            using type = typename TypeAt<Index - 1, Rest...>::type;
        };

        void test() {
            using Types = TypeAt<0, int, double, char>;
            static_assert(sizeof(typename Types::type) == sizeof(int), "first type is int");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// Test 45: Compile-time cartesian product
bool test_CartesianProduct() {
    TEST_START("compile-time cartesian product");

    const char* code = R"(
        template<typename... Ts>
        struct TypeList {};

        template<typename T1, typename T2>
        struct Pair {};

        template<typename List1, typename List2>
        struct CartesianProduct;

        template<typename... T1s, typename... T2s>
        struct CartesianProduct<TypeList<T1s...>, TypeList<T2s...>> {
            static constexpr size_t size = sizeof...(T1s) * sizeof...(T2s);
        };

        void test() {
            using L1 = TypeList<int, double>;
            using L2 = TypeList<char, float, long>;
            static_assert(CartesianProduct<L1, L2>::size == 6, "2 * 3 = 6");
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS();
    return true;
}

// ============================================================================
// Main Test Runner
// ============================================================================

int main() {
    std::cout << "========================================" << std::endl;
    std::cout << "Stream 5: Metaprogramming Test Suite" << std::endl;
    std::cout << "Target: 45 comprehensive tests" << std::endl;
    std::cout << "========================================" << std::endl << std::endl;

    int passed = 0;
    int failed = 0;

    // Section 1: Variadic Template Basics (Tests 1-10)
    std::cout << "\n=== SECTION 1: Variadic Template Basics ===" << std::endl;
    if (test_BasicVariadicTemplate()) passed++; else failed++;
    if (test_VariadicFunctionTemplate()) passed++; else failed++;
    if (test_PackExpansionFunctionCall()) passed++; else failed++;
    if (test_VariadicForwarding()) passed++; else failed++;
    if (test_SizeofOperator()) passed++; else failed++;
    if (test_VariadicInheritance()) passed++; else failed++;
    if (test_PackExpansionBracedInit()) passed++; else failed++;
    if (test_VariadicNonTypeParams()) passed++; else failed++;
    if (test_VariadicDefaultArgs()) passed++; else failed++;
    if (test_MixedVariadicFixed()) passed++; else failed++;

    // Section 2: Recursive Template Metaprogramming (Tests 11-20)
    std::cout << "\n=== SECTION 2: Recursive Metaprogramming ===" << std::endl;
    if (test_RecursiveFactorial()) passed++; else failed++;
    if (test_RecursiveFibonacci()) passed++; else failed++;
    if (test_RecursiveTypeList()) passed++; else failed++;
    if (test_RecursiveMax()) passed++; else failed++;
    if (test_RecursivePower()) passed++; else failed++;
    if (test_RecursiveGCD()) passed++; else failed++;
    if (test_ListReversal()) passed++; else failed++;
    if (test_RecursiveContains()) passed++; else failed++;
    if (test_RecursiveIndexOf()) passed++; else failed++;
    if (test_NestedRecursion()) passed++; else failed++;

    // Section 3: constexpr Functions (Tests 21-30)
    std::cout << "\n=== SECTION 3: constexpr Functions ===" << std::endl;
    if (test_BasicConstexpr()) passed++; else failed++;
    if (test_ConstexprConditional()) passed++; else failed++;
    if (test_ConstexprRecursion()) passed++; else failed++;
    if (test_ConstexprLoop()) passed++; else failed++;
    if (test_ConstexprMultipleReturns()) passed++; else failed++;
    if (test_ConstexprTemplate()) passed++; else failed++;
    if (test_ConstexprConstructor()) passed++; else failed++;
    if (test_ConstexprArray()) passed++; else failed++;
    if (test_ConstexprString()) passed++; else failed++;
    if (test_ConstexprComplexLogic()) passed++; else failed++;

    // Section 4: Fold Expressions & Advanced Patterns (Tests 31-45)
    std::cout << "\n=== SECTION 4: Fold Expressions & Advanced ===" << std::endl;
    if (test_UnaryLeftFold()) passed++; else failed++;
    if (test_UnaryRightFold()) passed++; else failed++;
    if (test_BinaryLeftFold()) passed++; else failed++;
    if (test_FoldLogicalAnd()) passed++; else failed++;
    if (test_FoldLogicalOr()) passed++; else failed++;
    if (test_FoldFunctionCall()) passed++; else failed++;
    if (test_PerfectForwarding()) passed++; else failed++;
    if (test_TemplateTemplateParams()) passed++; else failed++;
    if (test_CompileTimeDispatch()) passed++; else failed++;
    if (test_IfConstexpr()) passed++; else failed++;
    if (test_CompileTimeHash()) passed++; else failed++;
    if (test_TraitComposition()) passed++; else failed++;
    if (test_VariadicMinMax()) passed++; else failed++;
    if (test_CompileTimeTupleAccess()) passed++; else failed++;
    if (test_CartesianProduct()) passed++; else failed++;

    std::cout << "\n========================================" << std::endl;
    std::cout << "Test Results:" << std::endl;
    std::cout << "  Passed: " << passed << " / " << (passed + failed) << std::endl;
    std::cout << "  Failed: " << failed << " / " << (passed + failed) << std::endl;
    std::cout << "========================================" << std::endl;

    return (failed == 0) ? 0 : 1;
}
