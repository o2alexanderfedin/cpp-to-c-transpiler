#include "multidim_subscript.hpp"

namespace cpp23::multidim_subscript {

void test_multidim_subscript() {
    std::cout << "\n=== Testing Multidimensional Subscript Operator ===\n";

    // Test 1: 2D Matrix with [i, j]
    Matrix<int> mat(3, 3);
    for (std::size_t i = 0; i < 3; ++i) {
        for (std::size_t j = 0; j < 3; ++j) {
            mat[i, j] = i * 10 + j;
        }
    }

    std::cout << "Matrix[1, 2] = " << mat[1, 2] << "\n";
    std::cout << "Matrix[2, 1] = " << mat[2, 1] << "\n";

    // Test 2: 3D Tensor with [i, j, k]
    Tensor3D<int> tensor(2, 2, 2);
    tensor[0, 0, 0] = 1;
    tensor[0, 0, 1] = 2;
    tensor[0, 1, 0] = 3;
    tensor[1, 1, 1] = 8;

    std::cout << "Tensor[0, 0, 0] = " << tensor[0, 0, 0] << "\n";
    std::cout << "Tensor[1, 1, 1] = " << tensor[1, 1, 1] << "\n";

    // Test 3: Variadic subscript
    MultiArray<int> marr(100);
    marr[1, 2, 3] = 123;
    std::cout << "MultiArray[1, 2, 3] = " << marr[1, 2, 3] << "\n";

    // Test 4: Static subscript operator
    std::cout << "StaticLookup[5] = " << StaticLookup{}[5] << "\n";
    std::cout << "StaticLookup[7] = " << StaticLookup{}[7] << "\n";

    // Test 5: Const version
    const Matrix<int> cmat(2, 2);
    std::cout << "Const matrix[0, 0] = " << cmat[0, 0] << "\n";

    std::cout << "EXPECTED_OUTPUT: 12\n";
}

} // namespace cpp23::multidim_subscript
