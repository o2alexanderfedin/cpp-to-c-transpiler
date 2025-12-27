// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit14.C
// Category: constexpr-enhancements
// Test ID: 06
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct B {
  B() { }
  ~B() { }
};

struct T : B {
  constexpr ~T() { }
};

struct S {
  constexpr S() = default;              // was error: implicit S() is not constexpr, now OK
  ~S() noexcept(false) = default;       // OK, despite mismatched exception specification
private:
  int i;
  S(S&);                                // OK: private copy constructor
};

int main()
{
  // PR c++/106649
// P2448 - Relaxing some constexpr restrictions
// The definition of a constexpr destructor whose function-body is not
//  =delete shall additionally satisfy the following requirement:
//  (5.1) for every subobject of class type or (possibly multi-dimensional)
//  array thereof, that class type shall have a constexpr destructor.
S::S(S&) = default;                     // OK: defines copy constructor
  return 0;
}
