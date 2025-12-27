// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: static-operator-call4.C
// Category: static-operators
// Test ID: 04
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cstdlib>
// PR c++/107624

int n[3];
struct S {
  static void operator() (int x) { n[0] |= (1 << x); }
  static void baz (int x) { n[1] |= (1 << x); }
  int s;
};
volatile S s[2];

S &
foo (int x)
{
  static S t;
  n[2] |= (1 << x);
  return t;
}

int
main ()
{
  int i = 0;
  foo (0) (0);
  if (n[0] != 1 || n[1] || n[2] != 1)
    __builtin_abort ();
  foo (1).baz (1);
  if (n[0] != 1 || n[1] != 2 || n[2] != 3)
    __builtin_abort ();
  s[i++] (2);
  if (i != 1 || n[0] != 5 || n[1] != 2 || n[2] != 3)
    __builtin_abort ();
  s[--i].baz (3);
  if (i != 0 || n[0] != 5 || n[1] != 10 || n[2] != 3)
    __builtin_abort ();
}
