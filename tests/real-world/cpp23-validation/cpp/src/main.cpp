#include <iostream>
#include "deducing_this.hpp"
#include "consteval_if.hpp"
#include "multidim_subscript.hpp"
#include "static_operators.hpp"
#include "attributes.hpp"
#include "literals.hpp"

int main() {
    std::cout << "=================================================\n";
    std::cout << "  C++23 Feature Validation Test Suite\n";
    std::cout << "=================================================\n";

    try {
        // Core language features
        cpp23::deducing_this::test_deducing_this();
        cpp23::consteval_if::test_consteval_if();
        cpp23::multidim_subscript::test_multidim_subscript();
        cpp23::static_operators::test_static_operators();
        cpp23::attributes::test_attributes();
        cpp23::literals::test_literals();

        std::cout << "\n=================================================\n";
        std::cout << "  All tests completed successfully!\n";
        std::cout << "=================================================\n";

        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }
}
