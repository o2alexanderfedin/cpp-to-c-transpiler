#include "attributes.hpp"

namespace cpp23::attributes {

void test_attributes() {
    std::cout << "\n=== Testing C++23 Attributes ===\n";

    // Test 1: [[assume]] with division
    int result1 = divide_positive(100, 5);
    std::cout << "100 / 5 = " << result1 << "\n";

    // Test 2: [[assume]] with arrays
    int arr[] = {1, 2, 3, 4, 5};
    process_array(arr, 5);
    std::cout << "Array after doubling: ";
    for (int i = 0; i < 5; ++i) {
        std::cout << arr[i] << " ";
    }
    std::cout << "\n";

    // Test 3: Multiple assumptions
    int result2 = compute(3, 4);
    std::cout << "compute(3, 4) = " << result2 << "\n";

    // Test 4: Labeled blocks
    labeled_blocks();

    std::cout << "EXPECTED_OUTPUT: 20\n";
}

} // namespace cpp23::attributes
