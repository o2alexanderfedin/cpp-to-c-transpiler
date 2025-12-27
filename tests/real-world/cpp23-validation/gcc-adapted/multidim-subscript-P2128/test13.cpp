// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript6.C
// Category: multidim-subscript
// Test ID: 13
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
  int &operator[] (std::initializer_list<int> l, std::initializer_list<int> m) {
    int sum = 0;
    for (auto x : l)
      sum += x;
    for (auto x : m)
      sum += x;
    return a[sum];
  }
  int a[64];
};

int
main ()
{
  S s;
  if (&s[{0}, {3, 1, 2}] != &s.a[0 + 3 + 1 + 2]
      || &s[{42}, {11, 1}] != &s.a[42 + 11 + 1]
      || &s[{5, 7, 9}, {3}] != &s.a[5 + 7 + 9 + 3]
      || &s[{1, 2, 3, 4}, {3, 5, 8}] != &s.a[1 + 2 + 3 + 4 + 3 + 5 + 8])
    abort ();
}
