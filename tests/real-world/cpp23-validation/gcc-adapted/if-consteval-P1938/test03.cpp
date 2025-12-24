// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if11.C
// Category: if-consteval
// Test ID: 03
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

struct S {
  constexpr S () : s (0) {}
  consteval int foo () { return 1; }
  virtual consteval int bar () { return 2; }
  int s;
};


constexpr int
{
  if consteval {
    int (*fn1) () = foo;
    int (S::*fn2) () = &S::foo;
    int (S::*fn3) () = &S::bar;
    S s;
    return fn1 () + (s.*fn2) () + (s.*fn3) ();
  }
  return 0;
}

static_assert (bar () == 45);

int main()
{
  // PR c++/102753
consteval int foo () { return 42; }
bar ()
  return 0;
}
