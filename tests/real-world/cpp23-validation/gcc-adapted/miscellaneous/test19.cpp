// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: defaulted1.C
// Category: miscellaneous
// Test ID: 19
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct M
{
  M& operator=(M&);
};

struct T
{
  // if F1 is an assignment operator, and the return type of F1 differs
  // from the return type,  the program is ill-formed.
  T operator=(this T&, T&) = default;
  M m;
};

struct U
{
  // if F1's non-object parameter type is not a reference, the program
  // is ill-formed.
  U& operator=(this U&, U) = default;
  M m;
};

int main()
{
  // PR c++/116162
  return 0;
}
