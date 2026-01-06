// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/static_operators.cpp
// Header file

namespace cpp23 {
        namespace static_operators {
                class Calculator {
                public:
                        static int operator()(int a, int b) {
                                return a + b;
                        }
                };
                class SquareTable {
                public:
                        static int operator[](int n) {
                                return n * n;
                        }
                };
                class MathOps {
                public:
                        static double operator()(double x) {
                                return x * x;
                        }
                        static int operator[](int idx) {
                                static const int primes[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29};
                                return (idx >= 0 && idx < 10) ? primes[idx] : -1;
                        }
                };
                void test_static_operators();
        }
}
namespace cpp23 {
        namespace static_operators {
                void test_static_operators() {
                        Calculator calc;
                        SquareTable table;
                        MathOps ops;
                }
        }
}
void cpp23_static_operators_test_static_operators();
