// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript7.C
// Category: multidim-subscript
// Test ID: 14
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct S {
  int &operator[] (int, ...);
} s;
struct T {
  int &operator[] (auto...);
} t;
struct U {
  int &operator[] (...);
} u;

int main()
{
  // PR c++/103460
int a = s[1] + s[2, 1] + s[3, 2, 1] + s[4, 3, 2, 1]
	+ t[0.0] + t[nullptr, s, 42]
	+ u[] + u[42] + u[1.5L, 1LL];
  return 0;
}
