// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit17.C
// Category: constexpr-enhancements
// Test ID: 09
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

constexpr char
{
  static const int x = 5;
  static constexpr char c[] = "Hello World";
  return *(c + x);
}

static_assert (test () == ' ');

int main()
{
  // P2647R1 - Permitting static constexpr variables in constexpr functions
test ()
  return 0;
}
