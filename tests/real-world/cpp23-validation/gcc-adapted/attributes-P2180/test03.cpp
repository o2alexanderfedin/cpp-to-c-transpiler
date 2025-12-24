// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume10.C
// Category: attributes
// Test ID: 03
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>
#include <cstdlib>

struct string
{
  const char *p;
  int i;
  constexpr string (const char *p): p(p), i(0) { }
  constexpr int length () { ++i; return __builtin_strlen (p); }
};

constexpr int f()
{
  string s ("foobar");
  [[assume (s.length () > 0)]];
  if (s.i != 0) __builtin_abort();
  int len = s.length ();
  if (s.i != 1) __builtin_abort();
  return len;
}

static_assert (f());

int main()
{
  // Test that s.i is not modified by the assume.
  return 0;
}
