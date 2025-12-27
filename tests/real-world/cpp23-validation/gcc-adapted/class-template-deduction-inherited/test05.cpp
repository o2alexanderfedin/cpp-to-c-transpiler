// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: class-deduction-inherited4.C
// Category: class-template-deduction
// Test ID: 05
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class T>
struct A { A(T); };

template<class T>
struct B : A<T> {
  using B::A::A; // FIXME: we don't notice this inherited ctor
};

using ty1 = decltype(B(0));
using ty1 = B<int>;

template<class T=void>
struct C : A<int> {
  using A<int>::A;
};

using ty2 = decltype(C(0));
using ty2 = C<void>;

template<class T>
struct D : A<T> {
  using A<T>::A;
};

using ty3 = decltype(D(0));
using ty3 = D<int>;

using ty4 = decltype(D(0));
using ty4 = D<char>;

int main()
{
  A(int) -> A<char>; // FIXME: we need to rebuild the guides of D
  return 0;
}
