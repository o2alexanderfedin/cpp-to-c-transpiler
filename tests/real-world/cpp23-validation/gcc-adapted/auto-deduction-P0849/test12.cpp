// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast16.C
// Category: auto-deduction
// Test ID: 12
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

// PR c++/110025

template<auto V, class = decltype(auto(V)), class = decltype(auto{V})>
struct A { };

template<auto V>
A<V> f();

int main() {
  f<0>();
}
