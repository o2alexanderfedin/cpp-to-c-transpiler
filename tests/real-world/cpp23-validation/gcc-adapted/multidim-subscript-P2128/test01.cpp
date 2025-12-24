// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: explicit-obj-ops-mem-subscript.C
// Category: multidim-subscript
// Test ID: 01
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.




struct S {
  void operator[](this S&) {}
  void operator[](this S&, int) {}
  void operator[](this S&, int, int) {}
  template<typename... Args>
  void operator[](this S&, Args... args) {}
};

void non_dep()
{
  S s{};
  s[];
  s[0];
  s[0, 0];
  s[0, 0, 0];
}

template<typename = void>
void dependent()
{
  S s{};
  s[];
  s[0];
  s[0, 0];
  s[0, 0, 0];
}

void call()
{
  dependent();
}

int main()
{
  // P0847R7
// uses of member only operators (subscript)
// execution paths for subscript with 1 argument and 0 and 2+ arguments are different
// therefore we should additionally test the 0 and 2 argument cases as well
  return 0;
}
