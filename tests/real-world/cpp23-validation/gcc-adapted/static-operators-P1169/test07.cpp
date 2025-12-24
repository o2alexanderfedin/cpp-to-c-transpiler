// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: static-operator-call7.C
// Category: static-operators
// Test ID: 07
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

// PR c++/114632

struct S {};

auto lambda = [](auto, const int x) static /* -> void */ {};

int main()
{
    void (*func)(int, int) = lambda;
    return 0;
}
