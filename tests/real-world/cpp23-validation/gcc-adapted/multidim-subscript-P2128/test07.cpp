// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript14.C
// Category: multidim-subscript
// Test ID: 07
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cstdlib>
// PR c++/109319

struct A { static int &operator[] (int x) { static int a[2]; return a[x]; } };
struct B { int &operator[] (int x) { static int b[2]; return b[x]; } };
int c[2];

template <typename T, typename U, typename V>
int
foo ()
{
  A a;
  ++a[0, 1];
  B b;
  ++b[0, 1];
  ++c[0, 1];
  T d;
  ++d[0, 1];
  U e;
  ++e[0, 1];
  extern V f[2];
  ++f[0, 1];
  return 0;
}

int f[2];

int
main ()
{
  A a;
  ++a[0, 1];
  B b;
  ++b[0, 1];
  ++c[0, 1];
  foo <A, B, int> ();
  if (a.operator[] (1) != 3 || b.operator[] (1) != 3 || c[1] != 2 || f[1] != 1)
    __builtin_abort ();
}
