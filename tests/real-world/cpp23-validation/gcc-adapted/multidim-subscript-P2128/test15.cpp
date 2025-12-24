// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript8.C
// Category: multidim-subscript
// Test ID: 15
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct A
{
  void operator[](int, int = 42);
};

int main()
{
  // DR2507: Allow default arguments
  return 0;
}
