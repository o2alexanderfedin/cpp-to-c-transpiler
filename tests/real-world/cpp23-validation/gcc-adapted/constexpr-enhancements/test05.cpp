// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit13.C
// Category: constexpr-enhancements
// Test ID: 05
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


constexpr volatile int i = 10;

constexpr int
{
  return i;
}

constexpr int x = bar ();

int main()
{
  // PR c++/106649
// P2448 - Relaxing some constexpr restrictions
bar ()
  return 0;
}
