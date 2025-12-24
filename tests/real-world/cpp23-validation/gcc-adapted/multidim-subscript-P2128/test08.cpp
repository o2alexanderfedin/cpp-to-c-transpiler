// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript15.C
// Category: multidim-subscript
// Test ID: 08
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

template<class T, class... Ts>

static_assert(!CartesianIndexable<int>);
static_assert(!CartesianIndexable<int, int>);
static_assert(!CartesianIndexable<int, int, int>);

static_assert(!CartesianIndexable<int*>);
static_assert(CartesianIndexable<int*, int>);
static_assert(!CartesianIndexable<int*, int, int>);
static_assert(!CartesianIndexable<int*, int*>);

template<class... Ts>
struct A {
  void operator[](Ts...);
};

static_assert(!CartesianIndexable<A<>, int>);
static_assert(CartesianIndexable<A<int>, int>);
static_assert(!CartesianIndexable<A<int>>);
static_assert(!CartesianIndexable<A<int>, int, int>);
static_assert(CartesianIndexable<A<int, int>, int, int>);

int main()
{
  // PR c++/111493
concept CartesianIndexable = requires(T t, Ts... ts) { t[ts...]; };
  return 0;
}
