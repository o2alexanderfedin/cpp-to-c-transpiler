// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript2.C
// Category: multidim-subscript
// Test ID: 09
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct S
{
  S () : a {} {};
  int &operator[] () { return a[0]; }
  int &operator[] (int x) { return a[x]; }
  int &operator[] (int x, long y) { return a[x + y * 8]; }
  int a[64];
};

struct T
{
  operator int () { return 42; };
};


struct U
{
  operator int * () { return buf; }
};

struct V
{
  V () : a {} {};
  V (int x, int y, int z) : a {x, y, z} {};
  int &operator[] () { return a[0]; }
  int &operator[] (int x, long y) { return a[x + y * 8]; }
  int a[64];
};

{
  S s;
  T t;
  U u;
  V v;
  auto &a = buf[];
  auto &b = buf[1, 2];
  auto &c = s[1, 2, 3];
  auto &d = v[1];
  auto &e = v[1, 2, 3];
  auto &f = t[42, u];
  auto &g = u[42, t];
  auto &h = buf[42, 2.5];
}

int main()
{
  // P2128R6
int buf[64];
void
foo ()
  return 0;
}
