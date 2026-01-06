// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: static-operator-call8.C
// Category: static-operators
// Test ID: 08
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

// PR c++/119048

int main() {
	[] {}, [](...) static {};
}
