// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit6.C
// Category: constexpr-enhancements
// Test ID: 16
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


constexpr int
{
  goto lab;
lab:
  return 1;
}

constexpr int
{
  static int a;
  return ++a;
}

constexpr int
{
  thread_local int a;
  return ++a;
}


{
  constexpr int a = foo ();
  constexpr int b = bar ();
  constexpr int c = baz ();
}

int main()
{
  // P2242R3
foo ()
bar ()
baz ()
// In C++23, we get errors about the non-constant expressions only if we
// actually call the functions in a constexpr context.
void
test ()
  return 0;
}
