// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: class-deduction-inherited2.C
// Category: class-template-deduction
// Test ID: 03
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class T, class U, class V> struct F {
  F(T, U, V);       // #1
  F(T*, U*, V*);    // #2
  template<class W>
  F(int, int, W);   // #3
};


template<class T, class U> struct G : F<U, T, int> {
  using F<U, T, int>::F;
};

using ty1 = decltype(G(true, 'a', 1)); // uses #1
using ty1 = G<char, bool>;

using ty2 = decltype(G((bool*)0, (char*)0, (int*)0)); // uses #2
using ty2 = G<char, bool>;

using ty3 = decltype(G(0, 0, 0)); // uses #3
using ty3 = G<int, int>;

using ty4 = decltype(G(true, true, true)); // uses #4
using ty4 = G<void*, bool*>;

int main()
{
  F(bool, bool, bool) -> F<bool*, void*, int>;
  return 0;
}
