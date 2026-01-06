// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-array4.C
// Category: auto-deduction
// Test ID: 04
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


{
  auto x[i] = { 0 };
  auto(*p)[i] = (int(*)[i])0;
  int a[3];
  auto (*a1)[0/0] = &a;
}

int main()
{
  // PR c++/102414
// PR c++/101874
void
f (int i)
  return 0;
}
