// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast17.C
// Category: auto-deduction
// Test ID: 13
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class...> struct tuple;

template<auto V>
using constant_t = int;

template<auto... V>
using constants_t = tuple<constant_t<auto(V)>...>;

using ty0 = constants_t<>;
using ty1 = constants_t<1>;
using ty2 = constants_t<1, 2>;
using ty3 = constants_t<1, 2, 3>;

int main()
{
  // PR c++/110025
  return 0;
}
