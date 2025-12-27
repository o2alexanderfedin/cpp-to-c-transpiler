// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: static-operator-call3.C
// Category: static-operators
// Test ID: 03
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


{
  auto a = [] (auto x) static { return x; };
  int (*b) (int) = a;
}

int main()
{
  // P1169R4 - static operator()
void
foo ()
  return 0;
}
