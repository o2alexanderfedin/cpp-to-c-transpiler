// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume12.C
// Category: attributes
// Test ID: 05
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


{
  volatile int a = x;
  [[gnu::assume (x == (a & 0))]];
  return x;
}

int main()
{
  // PR middle-end/110754
int
foo (int x)
  return 0;
}
