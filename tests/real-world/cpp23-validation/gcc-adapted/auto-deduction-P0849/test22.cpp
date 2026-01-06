// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast9.C
// Category: auto-deduction
// Test ID: 22
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


void f1(decltype(new auto{0}));
void f2(decltype(new int{0}));

{
  int i;
  void f3(decltype(new auto{0}));
  void f4(decltype(new int{0}));
  f1 (&i);
  f2 (&i);
  f3 (&i);
  f4 (&i);
}

int main()
{
  // PR c++/103401
void
g ()
  return 0;
}
