// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast8.C
// Category: auto-deduction
// Test ID: 21
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


void f1 (decltype(auto(0)));
void f2 (decltype(auto{0}));
void f3 (int = auto(42));
void f4 (int = auto{42});
void f5 (decltype(auto(0)) = auto(42));
void f6 (auto (x));
void f7 (int[auto(10)]);
void f8 (int[auto{10}]);
void f9 (auto[auto{10}]);
void f10 (auto);
void f11 (int x, decltype(x) y);
void f12 (int[sizeof(auto{10})]);
void f13 (int[sizeof(auto(10))]);
void f14 (int[__extension__ alignof(auto{10})]);
void f15 (int[__extension__ alignof(auto(10))]);

{
  int a[2];
  f1 (1);
  f2 (1);
  f3 ();
  f3 (1);
  f4 ();
  f4 (1);
  f5 ();
  f5 (1);
  f6 ('a');
  f7 (&a[0]);
  f8 (&a[0]);
  f9 (&a[0]);
  f10 (1);
  f11 (1, 2);
  f12 (&a[0]);
  f13 (&a[0]);
  f14 (&a[0]);
  f15 (&a[0]);
}

int main()
{
  // PR c++/103401
void
g ()
  return 0;
}
