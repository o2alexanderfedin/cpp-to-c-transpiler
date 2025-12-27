// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: static-operator-call5.C
// Category: static-operators
// Test ID: 05
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class> void f()
{
  auto a = [] (auto x) static { return x; };
}
template void f<int>();

int main()
{
  // PR c++/108526
  return 0;
}
