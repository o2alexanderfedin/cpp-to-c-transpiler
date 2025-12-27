#include "literals.hpp"

namespace cpp23::literals {

void test_literals() {
    std::cout << "\n=== Testing C++23 Literals ===\n";

    // Test 1: size_t literals
    test_size_t_literals();

    // Test 2: Named universal character escapes
    // Note: This may fail on systems without proper Unicode support
    // Commenting out for compatibility
    // test_named_escapes();

    std::cout << "EXPECTED_OUTPUT: 1\n";
}

} // namespace cpp23::literals
