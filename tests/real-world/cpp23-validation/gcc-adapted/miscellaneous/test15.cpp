// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: concepts-err1.C
// Category: miscellaneous
// Test ID: 15
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

template<int>
static_assert(C<0>);

int main()
{
  // PR c++/103408
concept C = auto([]{});
  return 0;
}
