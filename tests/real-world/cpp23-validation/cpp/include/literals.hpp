#ifndef LITERALS_HPP
#define LITERALS_HPP

#include <iostream>
#include <cstddef>

namespace cpp23::literals {

// Feature: Literal suffix for size_t (uz/UZ) - P0330
// Feature: Named universal character escapes - P2071

inline void test_size_t_literals() {
    // C++23: uz/UZ suffix for size_t
    auto s1 = 42uz;          // std::size_t
    auto s2 = 100UZ;         // std::size_t
    auto s3 = 0xFFuz;        // std::size_t in hex

    std::cout << "Type check: " << std::is_same_v<decltype(s1), std::size_t> << "\n";
    std::cout << "42uz = " << s1 << "\n";
    std::cout << "100UZ = " << s2 << "\n";
    std::cout << "0xFFuz = " << s3 << "\n";
}

inline void test_named_escapes() {
    // C++23: Named universal character escapes
    // Note: Using correct Unicode character names
    const char* smiley = "\N{GRINNING FACE}";  // 😀
    const char* heart = "\N{HEAVY BLACK HEART}";  // ❤ (using correct name)

    std::cout << "Named escape sequences:\n";
    std::cout << "Smiley: " << smiley << "\n";
    std::cout << "Heart: " << heart << "\n";

    // Can also use in string literals
    std::string message = "Hello \N{WAVING HAND SIGN}";  // 👋 (using correct name)
    std::cout << "Message: " << message << "\n";
}

void test_literals();

} // namespace cpp23::literals

#endif // LITERALS_HPP
