// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-array3.C
// Category: auto-deduction
// Test ID: 03
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


constexpr int sz () { return 3; }

void f ()
{
  int a[3];
  const int N = 3;
  auto (*a2)[N] = &a;
  constexpr int M = 3;
  auto (*a3)[M] = &a;
  auto (*a4)[sz()] = &a;
}

int main()
{
  // PR c++/102414
// PR c++/101874
  return 0;
}
