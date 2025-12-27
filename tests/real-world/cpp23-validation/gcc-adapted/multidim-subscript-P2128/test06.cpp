// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript13.C
// Category: multidim-subscript
// Test ID: 06
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cstdlib>
// PR c++/108437

struct S { static int &operator[] (int x) { static int a[2]; return a[x]; } };
struct U { static int &operator[] (int x, int y, int z) { static int a[2]; return a[x + y + z]; } };
struct V { static int &operator[] () { static int a; return a; } };
int cnt;

template <typename T>
T &
bar (T &x)
{
  ++cnt;
  return x;
}

template <class T, class W, class X> void
foo ()
{
  S s;
  bar (s)[0]++;
  T t;
  bar (t)[0]++;
  U u;
  bar (u)[0, 0, 0]++;
  V v;
  bar (v)[]++;
  W w;
  bar (w)[0, 0, 0]++;
  X x;
  bar (x)[]++;
}

int
main ()
{
  S::operator[] (0) = 1;
  U::operator[] (0, 0, 0) = 2;
  V::operator[] () = 3;
  foo <S, U, V> ();
  if (S::operator[] (0) != 3 || U::operator[] (0, 0, 0) != 4 || V::operator[] () != 5 || cnt != 6)
    __builtin_abort ();
}
