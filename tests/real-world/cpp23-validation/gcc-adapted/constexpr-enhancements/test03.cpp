// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit11.C
// Category: constexpr-enhancements
// Test ID: 03
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.



struct Length {
  constexpr explicit Length(int i = 0) : val(i) { }
private:
  int val;
};

struct X {
  X() {}
  X(int i_) : i(i_) {}
  int i;
};

struct S {
  X x;
  // Calls a non-constexpr constructor X::X(int).
  constexpr S(int i) : x(i) { }
  S(int, int) { }
  // Target constructor isn't constexpr.
  constexpr S() : S(42, 42) { }
};

namespace N1 {
struct X {
  void x();
};
struct Y {
  X x;
  constexpr void y() { x.x(); }
};
}

void g();

struct A {
  constexpr A() { g(); }
};

struct B {
  constexpr B& operator=(const B&) { g(); return *this; }
  constexpr B& operator=(B&&) { g(); return *this; }
};

int main()
{
  // PR c++/106649
// P2448 - Relaxing some constexpr restrictions
// [dcl.constexpr]/4 used to say:
// The definition of a constexpr constructor whose function-body
// is not = delete shall additionally satisfy the following requirements:
// (4.1) for a non-delegating constructor, every constructor selected to initialize non-static data members and base class subobjects shall be a constexpr constructor;
// (4.2) for a delegating constructor, the target constructor shall be a constexpr constructor.
// This continues to be OK.
  return 0;
}
