// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume11.C
// Category: attributes
// Test ID: 04
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template <int ...args>
{
  [[assume (1 > 0)...]];
  [[assume (args > 0)...]];
#if __cpp_fold_expressions >= 201603L
  [[assume (((args > 0) && ...))]];
#endif
  [[gnu::assume (1 > 0)...]];
  [[gnu::assume (args > 0)...]];
#if __cpp_fold_expressions >= 201603L
  [[gnu::assume (((args > 0) && ...))]];
#endif
}

int main()
{
  // PR c++/109756
void
foo ()
  return 0;
}
