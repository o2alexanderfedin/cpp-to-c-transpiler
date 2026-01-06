// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit2.C
// Category: constexpr-enhancements
// Test ID: 12
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


constexpr int
{
lab:
  return 1;
}

constexpr int
{
  if (x)
    goto lab;
  return 1;
lab:
  return 0;
}

constexpr int
{
  if (!x)
    return 1;
  static int a;
  return ++a;
}

constexpr int
{
  if (!x)
    return 1;
  thread_local int a;
  return ++a;
}

struct S { S (); ~S (); int s; };

constexpr int
{
  if (!x)
    return 1;
  S s;
  return 0;
}

constexpr int a = bar (1);
constexpr int b = baz (1);
constexpr int c = qux (1);
constexpr int d = corge (1);

int main()
{
  // P2242R3
foo ()
bar (int x)
baz (int x)
qux (int x)
corge (int x)
  return 0;
}
