// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-array2.C
// Category: auto-deduction
// Test ID: 02
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class T> struct A { A(); };

int main()
{
  // PR c++/101988
A<int> a[3];
auto (*p)[3] = &a;
A<int> (*p2)[3] = &a;
A (*p3)[3] = &a;
auto (&r)[3] = a;
A<int> (&r2)[3] = a;
A (&r3)[3] = a;
  return 0;
}
