// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: charlit-encoding1.C
// Category: miscellaneous
// Test ID: 13
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cstdlib>
// PR c++/102615 - P2316R2 - Consistent character literal encoding

extern "C" void abort ();

int
main ()
{
#if ' ' == 0x20
  if (' ' != 0x20)
    abort ();
#elif ' ' == 0x40
  if (' ' != 0x40)
    abort ();
#else
  if (' ' == 0x20 || ' ' == 0x40)
    abort ();
#endif
#if 'a' == 0x61
  if ('a' != 0x61)
    abort ();
#elif 'a' == 0x81
  if ('a' != 0x81)
    abort ();
#elif 'a' == -0x7F
  if ('a' != -0x7F)
    abort ();
#else
  if ('a' == 0x61 || 'a' == 0x81 || 'a' == -0x7F)
    abort ();
#endif
  return 0;
}
