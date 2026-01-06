// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: decltype2.C
// Category: miscellaneous
// Test ID: 18
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>

template<typename T, typename U>
struct same_type { static const bool value = false; };

template<typename T>
struct same_type<T, T> { static const bool value = true; };

struct Widget {
  int x;
};


decltype(auto) fn0(Widget&& x) {
    return (::wg);
}
static_assert(same_type<decltype(fn0), Widget& (Widget&&)>::value);

decltype(auto) fn1(Widget&& x) {
    return ::wg;
}
static_assert(same_type<decltype(fn1), Widget (Widget&&)>::value);

decltype(auto) fn2() {
    Widget w;
    return w;
}
static_assert(same_type<decltype(fn2), Widget ()>::value);

decltype(auto) fn3() {
    Widget w;
    return (w);
}
static_assert(same_type<decltype(fn3), Widget&& ()>::value);

decltype(auto) fn4() {
    Widget w;
    return w.x;
}
static_assert(same_type<decltype(fn4), int ()>::value);

decltype(auto) fn5() {
    Widget w;
    return (w.x);
}
static_assert(same_type<decltype(fn5), int& ()>::value);

int main()
{
  // PR c++/101165 - P2266R1 - Simpler implicit move
// Test decltype(auto) more.
Widget wg;
  return 0;
}
