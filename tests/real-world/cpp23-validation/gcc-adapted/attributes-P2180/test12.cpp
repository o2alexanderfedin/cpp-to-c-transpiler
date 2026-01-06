// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume8.C
// Category: attributes
// Test ID: 12
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


{
  if (x == 1)
    goto l1;
  [[assume (({ l1:; 1; }))]];
}

int main()
{
  // PR tree-optimization/107369
void
foo (int x)
  return 0;
}
