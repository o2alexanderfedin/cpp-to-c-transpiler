// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if13.C
// Category: if-consteval
// Test ID: 05
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

// PR c++/115583

consteval int f(int i) {
  return i;
}
const bool b = 0;
constexpr int g(int i) {
  if consteval {
    return f(i);
  } else {
    return i;
  }
}
int main() {
  return g(1);
}
