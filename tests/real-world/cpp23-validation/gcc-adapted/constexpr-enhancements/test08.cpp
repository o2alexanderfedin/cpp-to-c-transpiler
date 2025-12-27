// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit16.C
// Category: constexpr-enhancements
// Test ID: 08
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template <typename T>
struct Wrapper {
    constexpr Wrapper() = default;
    constexpr Wrapper(Wrapper const&) = default;
    constexpr Wrapper(T const& t) : t(t) { }
    constexpr T get() const { return t; }
    constexpr bool operator==(Wrapper const&) const = default;
private:
    T t;
};

struct X {
    X();
    bool operator==(X const&) const;
};

int main()
{
  // PR c++/106649
// P2448 - Relaxing some constexpr restrictions

Wrapper<X> x;
  return 0;
}
