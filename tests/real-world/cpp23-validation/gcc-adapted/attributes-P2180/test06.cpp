// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume2.C
// Category: attributes
// Test ID: 06
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>
#include <stdexcept>

typedef int intx [[assume (true)]];

{
  int i;
  [[assume]];
  [[assume ()]];
  [[assume (true, true)]];
  [[assume (true)]] i = 1;
  [[assume (throw 1)]];
  [[assume (i = 1)]];
}

constexpr int
{
#if __cpp_constexpr >= 201304L
  [[assume (x == 42)]];
#endif
  return x;
}

constexpr int a = f2 (44);

{
  __asm ("" : "+r" (x));
  return x;
}

constexpr int
{
#if __cpp_constexpr >= 201304L
  [[assume (f3 (42) == 42)]];
#endif
  return x;
}

static_assert (f4 (42) == 42, "");

struct S {};

{
  S s;
  [[assume (s)]];
  return 0;
}

template <typename T>
{
  T t;
  [[assume (t)]];
  return 0;
}


constexpr int
{
#if __cpp_constexpr >= 201304L
  [[assume (x == 42 && y == 43 && z == 44 && w == 45)]];
#endif
  return x;
}

constexpr int w = f7 (42, 43, 45, 44);

int main()
{
  // P1774R8 - Portable assumptions
[[assume (true)]] void f1 ();
[[assume (true)]];
void
foo ()
f2 (int x)
int
f3 (int x)
f4 (int x)
int
f5 ()
int
f6 ()
int z = f6 <S> ();
f7 (int x, int y, int z, int w)
  return 0;
}
