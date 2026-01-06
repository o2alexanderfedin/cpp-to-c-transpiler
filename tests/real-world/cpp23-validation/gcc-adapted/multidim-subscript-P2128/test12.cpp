// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript5.C
// Category: multidim-subscript
// Test ID: 12
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cstdlib>
// P2128R6

#include <initializer_list>
#include <cstdlib>

struct S
{
  S () : a {} {};
  int &operator[] (std::initializer_list<int> l) {
    int sum = 0;
    for (auto x : l)
      sum += x;
    return a[sum];
  }
  int a[64];
};

int
main ()
{
  S s;
  if (&s[{0}] != &s.a[0]
      || &s[{42}] != &s.a[42]
      || &s[{5, 7, 9}] != &s.a[5 + 7 + 9]
      || &s[{1, 2, 3, 4}] != &s.a[1 + 2 + 3 + 4])
    abort ();
}
