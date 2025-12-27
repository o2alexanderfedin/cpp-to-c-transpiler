// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if4.C
// Category: if-consteval
// Test ID: 08
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


void f()
{
  goto l;
  if consteval
    {
    l:;
    }
}

void g()
{
  goto l;
  if not consteval
    {
    l:;
    }
}

void h()
{
  goto l;
  if consteval
    {
    }
  else
    {
    l:;
    }
}

void i()
{
  goto l;
  if not consteval
    {
    }
  else
    {
    l:;
    }
}
