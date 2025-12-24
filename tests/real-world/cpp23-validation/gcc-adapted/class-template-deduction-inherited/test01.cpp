// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: class-deduction-inherited1.C
// Category: class-template-deduction
// Test ID: 01
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template <typename T> struct B {
  B(T);
};
template <typename T> struct C : public B<T> {
  using B<T>::B;
};
template <typename T> struct D : public B<T> {};

using ty1 = decltype(c);
using ty1 = C<int>;


using ty2 = decltype(c2);
using ty2 = C<char>;

template <typename T> struct E : public B<int> {
  using B<int>::B;
};


template <typename T, typename U, typename V> struct F {
  F(T, U, V);
};
template <typename T, typename U> struct G : F<U, T, int> {
  using F<U, T, int>::F;
};

using ty3 = decltype(g);
using ty3 = G<char, bool>;

int main()
{
  // Modified example from P2582R1
B(bool) -> B<char>;
C c(42);            // OK, deduces C<int>
D d(42);
C c2(true);           // OK, deduces C<char>
E e(42);
G g(true, 'a', 1);  // OK, deduces G<char, bool>
  return 0;
}
