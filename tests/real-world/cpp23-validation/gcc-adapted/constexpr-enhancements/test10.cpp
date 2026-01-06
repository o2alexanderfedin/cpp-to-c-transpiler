// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit18.C
// Category: constexpr-enhancements
// Test ID: 10
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <stdexcept>

constexpr int
{
  if (x)
    throw 1;
  return 0;
}

constexpr int
{
  static const int a = f1 (1);
  return 0;
}

constexpr int
{
  static const int a = 5;
  return 0;
}

constexpr int
{
  static const int a = f1 (1);
  return 0;
}

constexpr int a4 = f4 ();

constexpr int
{
  static const int a = f1 (0);
  return 0;
}

constexpr int
{
  static const int a = f1 (0);
  return 0;
}

constexpr int a6 = f6 ();

int main()
{
  // P2647R1 - Permitting static constexpr variables in constexpr functions
f1 (int x)
f2 ()
f3 ()
f4 ()
f5 ()
f6 ()
  return 0;
}
