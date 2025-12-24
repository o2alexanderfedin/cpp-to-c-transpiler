// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: class-deduction-inherited3.C
// Category: class-template-deduction
// Test ID: 04
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class T>
struct A {
  A(T);
  template<class U> A(T, U);
};

template<class T>
struct B : A<const T> {
  using A<const T>::A;
};

using type = decltype(B(0));
using type = decltype(B(0, 0));
using type = B<int>;
