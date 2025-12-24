// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast11.C
// Category: auto-deduction
// Test ID: 07
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

static_assert(requires { auto(0); });
static_assert(requires { auto{0}; });

static_assert(requires { auto(auto(0)); });
static_assert(requires { auto{auto{0}}; });
static_assert(requires { auto(auto(auto(0))); });
static_assert(requires { auto{auto{auto{0}}}; });
static_assert(requires { requires auto(true); });
static_assert(requires { requires auto(auto(true)); });
static_assert(!requires { requires auto(false); });
static_assert(!requires { requires auto(auto(false)); });
auto f() requires (auto(false));

int main()
{
  // PR c++/103408
  return 0;
}
