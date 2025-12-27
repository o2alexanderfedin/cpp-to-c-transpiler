// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume4.C
// Category: attributes
// Test ID: 08
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>
#include <stdexcept>

typedef int intx [[__assume__ (true)]];
typedef int inty [[gnu::__assume__ (true)]];
typedef int intz __attribute__((assume (true)));//

{
  int i;
  [[__assume__]];
  [[__assume__ ()]];
  [[__assume__ (true, true)]];
  [[__assume__ (true)]] i = 1;
  [[__assume__ (throw 1)]];
  [[__assume__ (i = 1)]];
  [[gnu::assume]];
  [[gnu::assume ()]];
  [[gnu::assume (true, true)]];
  [[gnu::assume (true)]] i = 1;
  [[gnu::assume (throw 1)]];
  [[gnu::assume (i = 1)]];
  __attribute__((assume));
  __attribute__((assume ()));
  __attribute__((assume (true, true)));
  __attribute__((assume (true))) i = 1;
  __attribute__((assume (throw 1)));
  __attribute__((assume (i = 1)));
}

constexpr int
{
#if __cpp_constexpr >= 201304L
  [[__assume__ (x == 42)]];
#endif
  return x;
}

constexpr int
{
#if __cpp_constexpr >= 201304L
  [[gnu::__assume__ (x == 42)]];
#endif
  return x;
}

constexpr int
{
#if __cpp_constexpr >= 201304L
  __attribute__((__assume__ (x == 42)));//
#endif
  return x;
}

constexpr int a = f2 (44);
constexpr int aa = f2a (44);
constexpr int ab = f2b (44);

{
  __asm ("" : "+r" (x));
  return x;
}

constexpr int
{
#if __cpp_constexpr >= 201304L
  [[__assume__ (f3 (42) == 42)]];
#endif
  return x;
}

constexpr int
{
#if __cpp_constexpr >= 201304L
  [[gnu::assume (f3 (42) == 42)]];
#endif
  return x;
}

constexpr int
{
#if __cpp_constexpr >= 201304L
  __attribute__((assume (f3 (42) == 42)));
#endif
  return x;
}

static_assert (f4 (42) == 42, "");
static_assert (f4a (42) == 42, "");
static_assert (f4b (42) == 42, "");

struct S {};

{
  S s;
  [[gnu::assume (s)]];
  return 0;
}

template <typename T>
{
  T t;
  __attribute__((assume (t)));
  return 0;
}

int main()
{
  // P1774R8 - Portable assumptions
[[__assume__ (true)]] void f1 ();
[[__assume__ (true)]];
[[gnu::assume (true)]] void f1a ();
[[__gnu__::assume (true)]];
__attribute__((assume (true))) void f1b ();
void
foo ()
f2 (int x)
f2a (int x)
f2b (int x)
int
f3 (int x)
f4 (int x)
f4a (int x)
f4b (int x)
int
f5 ()
int
f6 ()
int z = f6 <S> ();
  return 0;
}
