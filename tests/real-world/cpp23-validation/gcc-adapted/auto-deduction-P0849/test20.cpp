// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast7.C
// Category: auto-deduction
// Test ID: 20
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

// PR c++/103401

void f(decltype(auto(0))) { }

int main()
{
  f<int,int>(0);
}
