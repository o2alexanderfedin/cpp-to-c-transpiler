// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast15.C
// Category: auto-deduction
// Test ID: 11
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


void foo (auto i, auto j);

struct A {
   A(int,int);
};

{
  A b1(auto(42), auto(42));
  A b2(auto(a), auto(42));
  A b3(auto(42), auto(a));
  A b4(auto(a),
       auto(a2));
  int v1(auto(42));
  int fn1(auto(a));
}

int main()
{
  // PR c++/112482
void
g (int a)
  return 0;
}
