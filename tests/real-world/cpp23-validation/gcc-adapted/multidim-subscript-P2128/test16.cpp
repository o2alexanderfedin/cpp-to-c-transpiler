// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript9.C
// Category: multidim-subscript
// Test ID: 16
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cstdlib>
// P2589R1

extern "C" void abort ();

struct S
{
  S () {};
  static int &operator[] () { return a[0]; }
  static int &operator[] (int x) { return a[x]; }
  static int &operator[] (int x, long y) { return a[x + y * 8]; }
  static int a[64];
};
int S::a[64];

int
main ()
{
  S s;
  for (int i = 0; i < 64; i++)
    s.a[i] = 64 - i;
  if (s[] != 64 || s[3] != 61 || s[4, 5] != 20)
    abort ();
  s[]++;
  s[42]++;
  ++s[3, 2];
  if (s.a[0] != 65 || s.a[42] != 23 || s.a[19] != 46)
    abort ();
}
