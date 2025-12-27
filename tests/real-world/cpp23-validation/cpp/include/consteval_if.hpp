#ifndef CONSTEVAL_IF_HPP
#define CONSTEVAL_IF_HPP

#include <iostream>
#include <string>

namespace cpp23::consteval_if {

// Feature: if consteval (P1938) - Compile-time evaluation detection
// Allows different behavior at compile-time vs runtime

consteval int compile_time_only(int x) {
    return x * x;
}

constexpr int flexible_compute(int x) {
    if consteval {
        // This branch executes only at compile-time
        return compile_time_only(x) + 1;
    } else {
        // This branch executes only at runtime
        return x * x + 1;
    }
}

// Useful for debugging/logging that disappears at compile-time
constexpr void debug_log(const char* msg) {
    if consteval {
        // No-op at compile-time (no I/O in constexpr context)
    } else {
        std::cout << "[DEBUG] " << msg << "\n";
    }
}

// Feature: consteval functions (immediate functions)
consteval int square_consteval(int x) {
    return x * x;
}

// Combining if consteval with constexpr
constexpr int compute_with_logging(int x) {
    if consteval {
        return x * 2;
    } else {
        std::cout << "Computing at runtime: " << x << "\n";
        return x * 2;
    }
}

// if !consteval syntax
constexpr int runtime_preferred(int x) {
    if !consteval {
        std::cout << "Runtime path\n";
        return x + 1;
    } else {
        return x + 1;
    }
}

void test_consteval_if();

} // namespace cpp23::consteval_if

#endif // CONSTEVAL_IF_HPP
