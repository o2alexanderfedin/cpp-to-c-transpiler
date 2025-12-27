// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if1.C
// Category: if-consteval
// Test ID: 01
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>
#include <cstdlib>
// P1938R3

extern "C" void abort ();

namespace std {
  constexpr inline bool
  is_constant_evaluated () noexcept
  {
    if consteval {
      return true;
    } else {
      return false;
    }
  }
}

consteval int foo (int x) { return x; }
consteval int bar () { return 2; }

constexpr int
baz (int x)
{
  int r = 0;
  if consteval
    {
      r += foo (x);
    }
  else
    {
      r += bar ();
    }
  if ! consteval
    {
      r += 2 * bar ();
    }
  else
    {
      r += foo (8 * x);
    }
  if (std::is_constant_evaluated ())
    r = -r;
  if consteval
    {
      r += foo (32 * x);
    }
  if not consteval
    {
      r += 32 * bar ();
    }
  return r;
}

template <typename T>
constexpr int
qux (T x)
{
  T r = 0;
  if consteval
    {
      r += foo (x);
    }
  else
    {
      r += bar ();
    }
  if ! consteval
    {
      r += 2 * bar ();
    }
  else
    {
      r += foo (8 * x);
    }
  if (std::is_constant_evaluated ())
    r = -r;
  if consteval
    {
      r += foo (32 * x);
    }
  if not consteval
    {
      r += 32 * bar ();
    }
  return r;
}

constexpr int a = baz (1);
static_assert (a == 23);
int b = baz (1);
constexpr int c = qux (1);
static_assert (c == 23);
int d = qux<int> (1);

int
main ()
{
  if (b != 23 || d != 23)
    abort ();
  if (baz (1) != 70 || qux (1) != 70 || qux (1LL) != 70)
    abort ();
}
