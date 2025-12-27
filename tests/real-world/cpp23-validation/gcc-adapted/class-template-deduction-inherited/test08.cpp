// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: class-deduction-inherited7.C
// Category: class-template-deduction
// Test ID: 08
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template <typename T, int _Extent = -1> struct span { span(T&&);};
template <typename T> span(T &&) -> span<T>;
template <typename et, int e = -1>
struct this_span : span<et, e> {
  using span<et, e>::span;
};
template <typename T> this_span(T &&) -> this_span<T>;

int main()
{
  // PR c++/117855
int vec;
this_span a = vec;
  return 0;
}
