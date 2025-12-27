// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit12.C
// Category: constexpr-enhancements
// Test ID: 04
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


constexpr unsigned int
{
  return *reinterpret_cast<unsigned const int *>(p);
}

constexpr void *
{
  return (void *) 1LL;
}

{
  constexpr int i = 42;
  constexpr auto a1 = fn0 (&i);
  constexpr auto a2 = fn1 (i);
}

int main()
{
  // PR c++/106649
// P2448 - Relaxing some constexpr restrictions
// Test that we get a diagnostic even in C++23 if you do call the function.
fn0 (const int *p)
fn1 (int i)
void
g ()
  return 0;
}
