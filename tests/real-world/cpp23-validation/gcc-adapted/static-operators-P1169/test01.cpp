// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: static-operator-call1.C
// Category: static-operators
// Test ID: 01
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

template <typename T>
struct S
{
  static constexpr bool operator () (T const &x, T const &y) { return x < y; };
  using P = bool (*) (T const &, T const &);
  operator P () const { return operator (); }
};

static_assert (S<int> {} (1, 2), "");

template <typename T>
{
  x (1, 2);
}

{
#if __cpp_constexpr >= 201603L
  auto a = [](int x, int y) static constexpr { return x + y; };
  static_assert (a (1, 2) == 3, "");
  bar (*a);
#endif
  auto b = []() static { return 1; };
  b ();
  auto c = [](int x, int y) static { return x + y; };
  c (1, 2);
  bar (*c);
#if __cpp_generic_lambdas >= 201707L
  auto d = []<typename T, typename U>(T x, U y) static { return x + y; };
  d (1, 2L);
#endif
  S<long> s;
  s(1L, 2L);
}

int main()
{
  // P1169R4 - static operator()
void
bar (T &x)
void
foo ()
  return 0;
}
