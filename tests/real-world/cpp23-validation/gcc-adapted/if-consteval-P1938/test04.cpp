// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if12.C
// Category: if-consteval
// Test ID: 04
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct S {
  constexpr S () : s (0) {}
  consteval int foo () { return 1; }
  virtual consteval int bar () { return 2; }
  int s;
};


constexpr int
{
  S s;
  if consteval {
    constexpr auto fn1 = foo;
    constexpr auto fn2 = &foo;
    constexpr auto fn3 = &S::foo;
    constexpr auto fn4 = &S::bar;
    constexpr auto fn5 = baz ();
    constexpr auto fn6 = qux ();
    constexpr auto fn7 = corge ();
    return fn1 () + fn2 () + (s.*fn3) () + (s.*fn4) () + fn5 () + (s.*fn6) () + (s.*fn7) ();
  }
  return 0;
}

int main()
{
  // PR c++/102753
consteval int foo () { return 42; }
consteval auto baz () { return foo; }
consteval auto qux () { return &S::foo; }
consteval auto corge () { return &S::bar; }
bar ()
auto a = bar ();
  return 0;
}
