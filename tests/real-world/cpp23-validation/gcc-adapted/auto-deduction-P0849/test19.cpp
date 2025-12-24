// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast6.C
// Category: auto-deduction
// Test ID: 19
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

void f (int);

{
  auto a1 = auto(f);
  auto a2 = auto{f};
  static_assert (__is_same_as (decltype (a1), void(*)(int)));
  static_assert (__is_same_as (decltype (a2), void(*)(int)));
}

int main()
{
  // PR c++/103049
// P0849R8 - auto(x)
void
g ()
  return 0;
}
