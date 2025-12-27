// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: static-operator-call2.C
// Category: static-operators
// Test ID: 02
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


{
  int u = 0;
  auto a = [](int x, int y) mutable mutable { return x + y; };
  auto b = [](int x, int y) static static { return x + y; };
  auto c = [](int x, int y) static mutable { return x + y; };
  auto d = [](int x, int y) mutable static { return x + y; };
  auto e = [=](int x, int y) static { return x + y; };
  auto f = [&](int x, int y) static { return x + y; };
  auto g = [u](int x, int y) static { return x + y; };
}

int main()
{
  // P1169R4 - static operator()
void
foo ()
  return 0;
}
