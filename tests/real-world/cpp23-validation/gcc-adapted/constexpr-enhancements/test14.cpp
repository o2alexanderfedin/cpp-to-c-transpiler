// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit4.C
// Category: constexpr-enhancements
// Test ID: 14
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


int qux ();

constexpr int
{
  switch (x)
    {
      static int v = qux ();
    case 12:
      return 1;
    }
  return 0;
}

constexpr int
{
  switch (x)
    {
      thread_local int v = qux ();
    case 12:
      return 1;
    }
  return 0;
}

constexpr int
{
  switch (x)
    {
      static const int v = qux ();
    case 12:
      return v;
    }
  return 0;
}

constexpr int
{
  switch (x)
    {
      const thread_local int v = qux ();
    case 12:
      return v;
    }
  return 0;
}

constexpr int a = foo (12);
constexpr int b = bar (12);
constexpr int c = baz (12);
constexpr int d = corge (12);

int main()
{
  foo (int x)
bar (int x)
baz (int x)
corge (int x)
  return 0;
}
