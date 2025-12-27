// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/multidim_subscript.cpp
// Header file

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
        namespace multidim_subscript {
                void test_multidim_subscript() {
                        Matrix<int> mat;
                        for (int i = <recovery-expr>(0); <recovery-expr>() < 3; ++<recovery-expr>()) {
                                for (int j = <recovery-expr>(0); <recovery-expr>() < 3; ++<recovery-expr>()) {
                                        <recovery-expr>(mat)[<recovery-expr>() , <recovery-expr>(j)] = <recovery-expr>() * 10 + <recovery-expr>();
                                }
                        }
                        Tensor3D<int> tensor;
                        <recovery-expr>(tensor)[0 , 0 , 0] = 1;
                        <recovery-expr>(tensor)[0 , 0 , 1] = 2;
                        <recovery-expr>(tensor)[0 , 1 , 0] = 3;
                        <recovery-expr>(tensor)[1 , 1 , 1] = 8;
                        MultiArray<int> marr;
                        <recovery-expr>(marr)[1 , 2 , 3] = 123;
                        const Matrix<int> cmat;
                }
        }
}
void cpp23_multidim_subscript_test_multidim_subscript();
