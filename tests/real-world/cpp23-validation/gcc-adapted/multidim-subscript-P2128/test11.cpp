// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript4.C
// Category: multidim-subscript
// Test ID: 11
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cstdlib>
// P2128R6

extern "C" void abort ();

struct S
{
  constexpr S () : a {} {};
  constexpr S (int x, int y, int z) : a {x, y, z} {};
  constexpr int &operator[] () { return a[0]; }
  constexpr int &operator[] (int x) { return a[x]; }
  constexpr int &operator[] (int x, long y) { return a[x + y * 8]; }
  int a[64];
};
int buf[26];

template <class ...Ts>
auto &
foo (S &s, Ts... args)
{
  return s[args...];
}

template <typename T, class ...Ts>
auto &
bar (T &s, Ts... args)
{
  return s[args...];
}

int
main ()
{
  S s;
  if (&foo (s) != &s.a[0]
      || &foo (s, 42) != &s.a[42]
      || &foo (s, 5, 4) != &s.a[37]
      || &bar (s) != &s.a[0]
      || &bar (s, 22) != &s.a[22]
      || &bar (s, 17, 3L) != &s.a[41]
      || &bar (buf, 5) != &buf[5])
    abort ();
}
