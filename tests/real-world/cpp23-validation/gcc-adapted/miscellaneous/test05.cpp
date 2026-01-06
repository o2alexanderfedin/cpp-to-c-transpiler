// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: Winvalid-utf8-2.C
// Category: miscellaneous
// Test ID: 05
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

int main()
{
  // P2295R6 - Support for UTF-8 as a portable source file encoding
// This test intentionally contains various byte sequences which are not valid UTF-8
// aÂß¿à í¿îðô¿¿a
// aa
// a¿a
// aÀa
// aÁa
// aõa
// aÿa
// aÂa
// aàa
// aà¿a
// aàa
// aà¿a
// aìa
// aí a
// aða
// að¿¿a
// aôa
// aý¿¿¿¿¿a
/* aÂß¿à í¿îðô¿¿a
/* aa
/* a¿a
/* aÀa
/* aÁa
/* aõa
/* aÿa
/* aÂa
/* aàa
/* aà¿a
/* aàa
/* aà¿a
/* aìa
/* aí a
/* aða
/* að¿¿a
/* aôa
/* aý¿¿¿¿¿a
/*
  return 0;
}
