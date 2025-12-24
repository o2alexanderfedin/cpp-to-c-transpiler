// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if10.C
// Category: if-consteval
// Test ID: 02
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.




constexpr int
{
  int r = 0;
  if consteval
    {
      auto y = [=] { foo (x); };
      y ();
    }
  return r;
}

template <typename T>
constexpr T
{
  T r = 0;
  if consteval
    {
      auto y = [=] { foo (x); };
      y ();
    }
  return r;
}

{
  return baz (x);
}

int main()
{
  // P1938R3
// We used to give errors but the lambdas are now promoted to consteval
// and are in a immediate function context, so no errors.
consteval int foo (int x) { return x; }
bar (int x)
baz (T x)
int
qux (int x)
  return 0;
}
