// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: range-for9.C
// Category: ranges
// Test ID: 10
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


#include <initializer_list>

template <typename _Tp> struct vector {
  vector(std::initializer_list<_Tp>);
  template <typename T> vector(T, T);
  char * begin();
  char * end();
};

struct f{
  f(const char*);
};

void h() {
  for (auto &vec : vector<vector<f>>{{""}})
    ;
}

int main()
{
  // PR c++/118856
  return 0;
}
