#include "consteval_if.hpp"

namespace cpp23::consteval_if {

void test_consteval_if() {
    std::cout << "\n=== Testing if consteval ===\n";

    // Test 1: Compile-time evaluation
    constexpr int ct_result = flexible_compute(5);
    std::cout << "Compile-time result: " << ct_result << "\n";

    // Test 2: Runtime evaluation
    int x = 5;
    int rt_result = flexible_compute(x);
    std::cout << "Runtime result: " << rt_result << "\n";

    // Test 3: Debug logging (only at runtime)
    debug_log("This appears only at runtime");

    // Test 4: consteval function (must be compile-time)
    constexpr int sq = square_consteval(7);
    std::cout << "Square (consteval): " << sq << "\n";

    // Test 5: Logging version
    constexpr int ct_logged = compute_with_logging(10);
    int rt_logged = compute_with_logging(10);
    std::cout << "Compile-time logged: " << ct_logged << "\n";
    std::cout << "Runtime logged: " << rt_logged << "\n";

    // Test 6: if !consteval
    int pref = runtime_preferred(42);
    std::cout << "Runtime preferred result: " << pref << "\n";

    std::cout << "EXPECTED_OUTPUT: 49\n";
}

} // namespace cpp23::consteval_if
