// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume7.C
// Category: attributes
// Test ID: 11
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <stdexcept>

{
  [[assume (x == 42)]];
  return x;
}

{
  [[assume (++x == 43)]];
  return x;
}

{
  [[assume (({ int z = ++x; static int w; ++w; if (z == 51) return -1; if (z == 53) goto lab1; if (z == 64) throw 1; z == 43; }))]];
lab1:
  return x;
}

struct S { S (); S (const S &); ~S (); int a, b; int foo (); };

{
  S s;
  [[assume (s.a == 42 && s.b == 43)]];
  return s.a + s.b;
}

{
  [[assume (a == 42 && b == 43)]];
  return a + b;
}

{
  [[assume (({ [[assume (x < 42)]]; x > -42; }))]];
  return x < 42;
}

{
  [[assume (({ [[assume (++x < 43)]]; x > -42; }))]];
  return x < 42;
}

int main()
{
  // P1774R8 - Portable assumptions
int
foo (int x)
int
bar (int x)
int
baz (int x)
int
qux ()
int
S::foo ()
int
corge (int x)
int
garply (int x)
  return 0;
}
