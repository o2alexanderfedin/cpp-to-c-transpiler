// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: charset1.C
// Category: miscellaneous
// Test ID: 14
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

#define S(x) # x
const char s1[] = S(Köppe);       // "Köppe"
const char s2[] = S(K\u00f6ppe);  // "Köppe"

static_assert (sizeof (s1) == 7);
static_assert (sizeof (s2) == 7);

int main()
{
  // P2314R4
  return 0;
}
