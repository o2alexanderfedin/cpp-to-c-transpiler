// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: static-operator-call6.C
// Category: static-operators
// Test ID: 06
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


auto foo () { return b (); }

int main()
{
  // PR c++/108525
auto b = [](...) static { return 1; };
  return 0;
}
