// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if2.C
// Category: if-consteval
// Test ID: 06
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


constexpr bool f()
{
  if consteval (true) {}
  if not consteval (false) {}
  if consteval if (true) {}
  if ! consteval {} else ;
  if consteval {} else if (true) {}
  if (true)
    if consteval
      {
      }
    else ;
  return false;
}


constexpr int
{
  int r = 0;
  if not consteval
    {
      r += foo (x);
    }
  else
    {
      r += bar ();
    }
  if consteval
    {
      r += 2 * bar ();
    }
  else
    {
      r += foo (8 * x);
    }
  if ! consteval
    {
      r += foo (32 * x);//
    }
  if consteval
    {
      r += 32 * bar ();
    }
  return r;
}

template <typename T>
constexpr int
{
  int r = 0;
  if not consteval
    {
      r += foo (x);
    }
  else
    {
      r += bar ();
    }
  if consteval
    {
      r += 2 * bar ();
    }
  else
    {
      r += foo (8 * x);
    }
  if ! consteval
    {
      r += foo (32 * x);//
    }
  if consteval
    {
      r += 32 * bar ();
    }
  return r;
}

template <typename T>
constexpr T
{
  T r = 0;
  if not consteval
    {
      r += foo (x);
    }
  else
    {
      r += bar ();
    }
  if consteval
    {
      r += 2 * bar ();
    }
  else
    {
      r += foo (8 * x);
    }
  if ! consteval
    {
      r += foo (32 * x);
    }
  if consteval
    {
      r += 32 * bar ();
    }
  return r;
}

{
  return corge (x);
}

int main()
{
  // P1938R3
consteval int foo (int x) { return x; }
consteval int bar () { return 2; }
baz (int x)
// This function is not instantiated so NDR.
qux (int x)
corge (T x)
int
garply (int x)
  return 0;
}
