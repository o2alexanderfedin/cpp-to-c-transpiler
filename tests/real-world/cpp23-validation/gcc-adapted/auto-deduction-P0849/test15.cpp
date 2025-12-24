// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast2.C
// Category: auto-deduction
// Test ID: 15
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

struct X { };

void h()
{
  double v[] = { 1.2, 3.4 };
  +auto(v);
  +auto{v};
  static_assert (__is_same_as (decltype (auto(v)), double *));
  static_assert (__is_same_as (decltype (auto{v}), double *));
  auto a1 = fn ();
  static_assert (__is_same_as (decltype (auto(fn())), decltype (a1)));
  static_assert (__is_same_as (decltype (auto{fn()}), decltype (a1)));
  auto a2 = fnr ();
  static_assert (__is_same_as (decltype (auto(fnr())), decltype (a2)));
  static_assert (__is_same_as (decltype (auto{fnr()}), decltype (a2)));
  +auto(1);
  new auto(1);
  +auto{1};
  new auto{1};
}

template<typename T>
void baz (T t, const T &tr, T &&trr)
{
  +auto(t);
  +auto{t};
  +auto(tr);
  +auto{tr};
  +auto(trr);
  +auto{trr};
  static_assert (__is_same_as (decltype (auto(t)), T));
  static_assert (__is_same_as (decltype (auto{t}), T));
  static_assert (__is_same_as (decltype (auto(tr)), T));
  static_assert (__is_same_as (decltype (auto{tr}), T));
  static_assert (__is_same_as (decltype (auto(trr)), T));
  static_assert (__is_same_as (decltype (auto{trr}), T));
}

template<typename = decltype(auto(1))>
void foo ()
{
}

template<int = auto(1)>
void bar ()
{
}

{
  foo<>();
  bar<>();
  int i = 42;
  baz (1, i, 42);
}

int main()
{
  // PR c++/103049
// P0849R8 - auto(x)
X& fn ();
X&& fnr ();
void
g()
  return 0;
}
