// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: constexpr-nonlit8.C
// Category: constexpr-enhancements
// Test ID: 18
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <stdexcept>

struct NonLiteral {
  NonLiteral() {}
};

constexpr NonLiteral
{
  return NonLiteral{};
}

constexpr int
{
  return 42;
}

void f(int& i) {
    i = 0;
}

constexpr void g(int& i) {
    f(i);
}

constexpr int f(bool b)
constexpr int f() { return f(true); }   // ill-formed, no diagnostic required

struct B {
  constexpr B(int) : i(0) { }
  int i;
};


struct D : B {
  constexpr D() : B(global) { }
  // ill-formed, no diagnostic required
  // lvalue-to-rvalue conversion on non-constant global
};

template<typename>
constexpr void
{
  int i = 42;
  f (i);
}

{
  fn2<int>();
}

constexpr volatile int cvi = 10;

constexpr int
{
  return cvi;
}

constexpr unsigned int
{
  unsigned int *q = reinterpret_cast<unsigned int *>(p);
  return *q;
}

constexpr int
{
  void *p = (void *) 1LL;
  return 42;
}

constexpr int
{
  static int s = i;
  return s;
}

int main()
{
  // PR c++/106649
// P2448 - Relaxing some constexpr restrictions
// No constexpr constructors = not a literal type.
// C++23: It is possible to write a constexpr function for which no
// invocation satisfies the requirements of a core constant expression.
fn0 (int)
fn1 (NonLiteral)
// From P2448.
// [dcl.constexpr] used to have this.
  { return b ? throw 0 : 0; }           // OK
int global;
// If no specialization of the template would satisfy the requirements
// for a constexpr function when considered as a non-template function,
// the template is ill-formed, no diagnostic required.
fn2 ()
void
fn3 ()
fn4 ()
fn5 (int *p)
fn6 (int i)
fn7 (int i)
  return 0;
}
