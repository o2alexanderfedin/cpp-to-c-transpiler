// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast10.C
// Category: auto-deduction
// Test ID: 06
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

struct S {
  int i1 : auto(12);
  int i2 : auto{12};
  static constexpr auto x = auto(12);
  static constexpr auto y = auto{12};
};

struct R {
  int i;
};

static constexpr R r1 = { auto(23) };
static constexpr R r2 = { auto{23} };
static_assert (auto(true));
static_assert (auto{true});

int main()
{
  enum E { X = auto(12), Y = auto{1u} };
  return 0;
}
