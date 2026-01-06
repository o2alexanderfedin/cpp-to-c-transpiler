// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit7.C
// Category: constexpr-enhancements
// Test ID: 17
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


constexpr bool foo () { extern thread_local int t; return true; }
static constexpr bool a = foo ();

int main()
{
  // PR c++/104994
// CWG2552
  return 0;
}
