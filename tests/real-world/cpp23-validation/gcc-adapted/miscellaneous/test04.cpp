// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: Winvalid-utf8-12.C
// Category: miscellaneous
// Test ID: 04
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


#define I(x)

int main()
{
  // P2295R6 - Support for UTF-8 as a portable source file encoding
// This test intentionally contains various byte sequences which are not valid UTF-8
I(Âß¿à í¿îðô¿¿)
I()
I(¿)
I(À)
I(Á)
I(õ)
I(ÿ)
I(Â)
I(à)
I(à¿)
I(à)
I(à¿)
I(ì)
I(í )
I(ð)
I(ð¿¿)
I(ô)
I(ý¿¿¿¿¿)
  return 0;
}
