// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast3.C
// Category: auto-deduction
// Test ID: 16
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


{
  char x[] = "foo";
  +decltype(auto){x};
  +decltype(auto)(x);
  +auto();
  new auto();
  +auto{};
  new auto{};
  +auto(1, 2);
  new auto(1, 2);
  +auto{1, 2};
  new auto{1, 2};
}

int main()
{
  // PR c++/103049
// P0849R8 - auto(x)
// Test invalid use.
void
f ()
  return 0;
}
