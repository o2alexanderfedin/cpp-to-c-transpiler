// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit15.C
// Category: constexpr-enhancements
// Test ID: 07
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

struct S {
  constexpr S() {}
  S& operator=(const S&) = default;
  S& operator=(S&&) = default;
};

struct U {
  constexpr U& operator=(const U&) = default;
  constexpr U& operator=(U&&) = default;
};

constexpr void
{
  S a;
  S b;
  b = a;
  b = S{};
  U u, v;
  u = v;
  u = U{};
}

static_assert ((g(), true), "");

int main()
{
  // PR c++/106649
// P2448 - Relaxing some constexpr restrictions
// A copy/move assignment operator for a class X that is defaulted and
// not defined as deleted is implicitly defined when it is odr-used,
// when it is needed for constant evaluation, or when it is explicitly
// defaulted after its first declaration.
// The implicitly-defined copy/move assignment operator is constexpr.
g ()
  return 0;
}
