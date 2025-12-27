// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast1.C
// Category: auto-deduction
// Test ID: 05
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct A {};
void f(A&) = delete;  // #1
void f(A&&); // #2
void h() {
//  f(g());      // calls #1
  f(A(g()));     // calls #2 with a temporary object
  f(auto(g()));  // calls #2 with a temporary object
}

int main()
{
  // PR c++/103049
// P0849R8 - auto(x)
// Testcase from P0849R8.
A& g();
  return 0;
}
