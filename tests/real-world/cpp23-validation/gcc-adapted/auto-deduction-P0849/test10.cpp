// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast14.C
// Category: auto-deduction
// Test ID: 10
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct A {
   A(int,int);
};

int main()
{
  // PR c++/112410
int a;
A b1(auto(a), 42);
  return 0;
}
