#include "static_operators.hpp"

namespace cpp23::static_operators {

void test_static_operators() {
    std::cout << "\n=== Testing Static Operators ===\n";

    // Test 1: Static operator()
    Calculator calc;
    std::cout << "Calculator()(5, 3) = " << calc(5, 3) << "\n";
    std::cout << "Calculator()(10, 20) = " << Calculator{}(10, 20) << "\n";

    // Test 2: Static operator[]
    SquareTable table;
    std::cout << "SquareTable[5] = " << table[5] << "\n";
    std::cout << "SquareTable[12] = " << SquareTable{}[12] << "\n";

    // Test 3: Combined static operators
    MathOps ops;
    std::cout << "MathOps()(7.5) = " << ops(7.5) << "\n";
    std::cout << "MathOps[3] = " << ops[3] << "\n";
    std::cout << "MathOps[5] = " << MathOps{}[5] << "\n";

    std::cout << "EXPECTED_OUTPUT: 8\n";
}

} // namespace cpp23::static_operators
