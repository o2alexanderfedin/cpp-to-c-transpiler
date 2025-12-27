// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit19.C
// Category: constexpr-enhancements
// Test ID: 11
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

struct A { ~A(); };

struct B {
  constexpr B() {
    A a;
    for (int i = 0; i < 10; i++) { }
  }
};

constexpr bool f() {
  B b;
  return true;
}

static_assert(f());
