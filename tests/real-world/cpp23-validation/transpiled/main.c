// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/main.cpp
// Implementation file

#include "main.h"

namespace cpp23 {
        namespace deducing_this {
                class TextBuffer {
                private:
                        int data_;
                public:
                        TextBuffer(int data) {
                        }
                        template <typename Self> auto &&get(this Self &&self) {
                                if (<recovery-expr>()) {
                                }
                                if (<recovery-expr>()) {
                                } else {
                                }
                        }
                        void print(this const TextBuffer &self) {
                        }
                        void modify(this TextBuffer self) {
                                <recovery-expr>(self) += " [modified]";
                        }
                };
                template <typename T> class CRTPBase {
                public:
                        void interface(this int &&self) {
                        }
                };
                class CRTPDerived {
                public:
                        void implementation() {
                        }
                };
                inline class (lambda at /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/deducing_this.hpp:69:12) factorial_lambda() {
                        return [](auto self, int n) mutable -> int {
                                if (n <= 1)
                                        return 1;
                                return n * self(n - 1);
                        };
                }
                void test_deducing_this();
        }
}
namespace cpp23 {
        namespace consteval_if {
                int compile_time_only(int x) {
                        return x * x;
                }
                constexpr int flexible_compute(int x) {
                }
                constexpr void debug_log(const char *msg) {
                }
                int square_consteval(int x) {
                        return x * x;
                }
                constexpr int compute_with_logging(int x) {
                }
                constexpr int runtime_preferred(int x) {
                }
                void test_consteval_if();
        }
}
namespace cpp23 {
        namespace multidim_subscript {
                template <typename T> class Matrix {
                private:
                        int data_;
                        int rows_;
                        int cols_;
                public:
                        Matrix<T>(int rows, int cols) {
                        }
                        T &operator[](int row, int col) {
                        }
                        const T &operator[](int row, int col) const {
                        }
                        T &operator[](int idx) {
                        }
                        int rows() const {
                        }
                        int cols() const {
                        }
                };
                template <typename T> class Tensor3D {
                private:
                        int data_;
                        int dim1_;
                        int dim2_;
                        int dim3_;
                public:
                        Tensor3D<T>(int d1, int d2, int d3) {
                        }
                        T &operator[](int i, int j, int k) {
                        }
                        const T &operator[](int i, int j, int k) const {
                        }
                };
                template <typename T> class MultiArray {
                private:
                        int data_;
                public:
                        explicit MultiArray<T>(int size) {
                        }
                        template <typename ...Indices> T &operator[](Indices ...indices) {
                                int idx = <recovery-expr>(0);
                                int mult = <recovery-expr>(1);
                                ((<recovery-expr>(idx) += indices * <recovery-expr>() , <recovery-expr>(mult) *= 10) , ...);
                        }
                };
                class StaticLookup {
                public:
                        static int operator[](int key) {
                                return key * key;
                        }
                };
                void test_multidim_subscript();
        }
}
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
        namespace attributes {
                inline int divide_positive(int a, int b) {
[[assume(b > 0)]]                        ;
                        return a / b;
                }
                inline void process_array(int *arr, int size) {
[[assume(arr != nullptr)]]                        ;
[[assume(size > 0)]]                        ;
                        for (int i = 0; i < size; ++i) {
                                arr[i] *= 2;
                        }
                }
                inline int compute(int x, int y) {
[[assume(x >= 0)]]                        ;
[[assume(y >= 0)]]                        ;
[[assume(x + y < 1000)]]                        ;
                        return x * x + y * y;
                }
                inline void labeled_blocks() {
                        bool done = false;
                        if (done)
                                goto block1_end;
                        {
                        }
                      block1_end:
                        ;
                        if (done)
                                goto block2_end;
                        {
                        }
                      block2_end:
                        ;
                }
                void test_attributes();
        }
}
namespace cpp23 {
        namespace literals {
                inline void test_size_t_literals() {
                        auto s1 = 42UL;
                        auto s2 = 100UL;
                        auto s3 = 255UL;
                }
                inline void test_named_escapes() {
                        const char *smiley = "\360\237\230\200";
                        const char *heart = "\342\235\244";
                        int message = <recovery-expr>("Hello \360\237\221\213");
                }
                void test_literals();
        }
}
int main() {
        try {
                cpp23::deducing_this::test_deducing_this();
                cpp23::consteval_if::test_consteval_if();
                cpp23::multidim_subscript::test_multidim_subscript();
                cpp23::static_operators::test_static_operators();
                cpp23::attributes::test_attributes();
                cpp23::literals::test_literals();
                return 0;
        } catch (const int &e) {
                return 1;
        }
}

int main() {
        try {
                cpp23::deducing_this::test_deducing_this();
                cpp23::consteval_if::test_consteval_if();
                cpp23::multidim_subscript::test_multidim_subscript();
                cpp23::static_operators::test_static_operators();
                cpp23::attributes::test_attributes();
                cpp23::literals::test_literals();
                return 0;
        } catch (const int &e) {
                return 1;
        }
}

