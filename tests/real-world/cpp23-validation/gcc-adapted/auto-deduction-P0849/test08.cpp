// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast12.C
// Category: auto-deduction
// Test ID: 08
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class T>

int main()
{
  // PR c++/104752
concept C = true;
auto x = auto(1);     // valid (P0849R8)
auto y = C auto(1);
auto z = C auto{1};
  return 0;
}
