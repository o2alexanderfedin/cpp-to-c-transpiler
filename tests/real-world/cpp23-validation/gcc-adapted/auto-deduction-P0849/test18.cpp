// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast5.C
// Category: auto-deduction
// Test ID: 18
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


struct X {
  X() = default;
  X(const X&) = delete;
};

{
  X x;
  +X(x);
  +auto(x);
}

class A;
void f(A);

class A {
    int x;
public:
    A();
    auto run() {
        f(A(*this));
        f(auto(*this));
    }
protected:
    A(const A&);
};

void z () {
  A a;
  a.run ();
}

int main()
{
  // PR c++/103049
// P0849R8 - auto(x)
void
g ()
  return 0;
}
