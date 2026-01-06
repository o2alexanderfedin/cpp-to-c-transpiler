// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: class-deduction-inherited10.C
// Category: class-template-deduction
// Test ID: 02
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class T> struct A { A(T) {}; };

using B = A<int>;

template<class T=void>
struct C : B { using B::B; };

int main()
{
  // PR c++/122070
C c = 0;
  return 0;
}
