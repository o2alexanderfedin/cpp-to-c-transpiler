// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume9.C
// Category: attributes
// Test ID: 13
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

struct string
{
  const char *p;
  constexpr string (const char *p): p(p) { }
  constexpr int length () { return __builtin_strlen (p); }
};

constexpr int f()
{
  string s ("foobar");
  [[assume (s.length () == 0)]];
  return s.length ();
}

static_assert (f());

int main()
{
  // Diagnose failed assumptions involving a function call.
  return 0;
}
