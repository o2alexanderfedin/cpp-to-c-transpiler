// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: decltype1.C
// Category: miscellaneous
// Test ID: 17
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

template<typename T, typename U>
struct same_type { static const bool value = false; };

template<typename T>
struct same_type<T, T> { static const bool value = true; };

auto f1(int x) -> decltype(x) { return (x); }
static_assert(same_type<decltype(f1), int (int)>::value);
auto f2(int x) -> decltype((x)) { return (x); }
static_assert(same_type<decltype(f2), int& (int)>::value);
auto f3(int x) -> decltype(auto) { return (x); }
static_assert(same_type<decltype(f3), int&& (int)>::value);
auto g1(int x) -> decltype(x) { return x; }
static_assert(same_type<decltype(g1), int (int)>::value);
auto g2(int x) -> decltype((x)) { return x; }
static_assert(same_type<decltype(g2), int& (int)>::value);
auto g3(int x) -> decltype(auto) { return x; }
static_assert(same_type<decltype(g3), int (int)>::value);


struct X { };

{
  return x;
}
static_assert(same_type<decltype(f4), X(X)>::value);

{
  return x;
}
static_assert(same_type<decltype(f5), X&(X)>::value);

{
  return x;
}
static_assert(same_type<decltype(f6), X&&(X)>::value);

{
  return (x);
}
static_assert(same_type<decltype(f7), X(X)>::value);

{
  return (x);
}
static_assert(same_type<decltype(f8), X&(X)>::value);

{
  return (x);
}
static_assert(same_type<decltype(f9), X&&(X)>::value);

{
  return x;
}
static_assert(same_type<decltype(f10), X(X)>::value);

{
  return (x);
}
static_assert(same_type<decltype(f11), X&&(X)>::value);

{
  return x;
}
static_assert(same_type<decltype(f12), X&(X&)>::value);

{
  return (x);
}
static_assert(same_type<decltype(f13), X&(X&)>::value);

{
  return x;
}
static_assert(same_type<decltype(f14), X&&(X&&)>::value);

{
  return (x);
}
static_assert(same_type<decltype(f15), X&&(X&&)>::value);

int main()
{
  // PR c++/101165 - P2266R1 - Simpler implicit move
// Tests from P2266R1, decltype-related changes in
// $ 3.2.1. Interaction with decltype and decltype(auto)
// Note that f2 and g2 are well-formed in C++20, but we propose to make
// f2 and g2 ill-formed, because they attempt to bind an lvalue reference
// to a move-eligible xvalue expression.
auto
f4 (X x)
auto&
f5 (X x)
auto&&
f6 (X x)
auto
f7 (X x)
auto&
f8 (X x)
auto&&
f9 (X x)
decltype(auto)
f10 (X x)
decltype(auto)
f11 (X x)
decltype(auto)
f12 (X& x)
decltype(auto)
f13 (X& x)
decltype(auto)
f14 (X&& x)
decltype(auto)
f15 (X&& x)
  return 0;
}
