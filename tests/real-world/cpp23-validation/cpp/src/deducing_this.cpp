#include "deducing_this.hpp"

namespace cpp23::deducing_this {

void test_deducing_this() {
    std::cout << "\n=== Testing Deducing This ===\n";

    // Test 1: Lvalue reference
    TextBuffer buf1("Hello");
    auto& ref = buf1.get();
    std::cout << "Lvalue ref: " << ref << "\n";

    // Test 2: Const lvalue reference
    const TextBuffer buf2("World");
    auto& cref = buf2.get();
    std::cout << "Const lvalue ref: " << cref << "\n";

    // Test 3: Rvalue reference
    auto&& rref = TextBuffer("Temporary").get();
    std::cout << "Rvalue ref: " << rref << "\n";

    // Test 4: Explicit object parameter with specific type
    buf1.print();

    // Test 5: By-value explicit object parameter
    buf1.modify();
    buf1.print(); // Original unchanged

    // Test 6: Simplified CRTP
    CRTPDerived derived;
    derived.interface();

    // Test 7: Recursive lambda with deducing this
    auto fact = factorial_lambda();
    std::cout << "Factorial(5) = " << fact(5) << "\n";

    std::cout << "EXPECTED_OUTPUT: 120\n";
}

} // namespace cpp23::deducing_this
