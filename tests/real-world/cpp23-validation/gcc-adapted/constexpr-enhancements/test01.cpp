// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit1.C
// Category: constexpr-enhancements
// Test ID: 01
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

constexpr int
{
lab:
  return 1;
}

constexpr int
{
  if (x)
    goto lab;
  return 1;
lab:
  return 0;
}

constexpr int
{
  if (!x)
    return 1;
  static int a;
  return ++a;
}

constexpr int
{
  if (!x)
    return 1;
  thread_local int a;
  return ++a;
}

constexpr int
{
  if (!x)
    return 1;
  extern thread_local int a;
  return ++a;
}

struct S { S (); ~S (); int s; };

constexpr int
{
  if (!x)
    return 1;
  S s;
  return 0;
}

static_assert (foo ());
static_assert (bar (0));
static_assert (baz (0));
static_assert (qux (0));
static_assert (garply (0));
static_assert (corge (0));

int main()
{
  // P2242R3
foo ()
bar (int x)
baz (int x)
qux (int x)
garply (int x)
corge (int x)
#if __cpp_constexpr >= 202110L
#endif
  return 0;
}
