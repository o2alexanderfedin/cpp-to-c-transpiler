// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: subscript11.C
// Category: multidim-subscript
// Test ID: 04
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct S {
  static int &operator[] (int);
  static int &operator[] ();
  static int &operator[] (int, int, int);
  int s;
};
