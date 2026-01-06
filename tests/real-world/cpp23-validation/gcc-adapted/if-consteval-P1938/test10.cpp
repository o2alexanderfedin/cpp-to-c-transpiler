// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if6.C
// Category: if-consteval
// Test ID: 10
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


void f()
{
  if consteval
    {
      goto l;
    l:;
    }
  else
    {
      goto l2;
    l2:;
    }
}
