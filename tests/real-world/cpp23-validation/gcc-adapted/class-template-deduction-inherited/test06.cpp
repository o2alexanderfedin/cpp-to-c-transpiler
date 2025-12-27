// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: class-deduction-inherited5.C
// Category: class-template-deduction
// Test ID: 06
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template<class T>
struct Base1 { };

template<class T>
struct Base2 { };

template<class T = int>
struct Derived : public Base1<T>, Base2<T> {
  using Base1<T>::Base1;
  using Base2<T>::Base2;
};


template<class T = int>
struct Derived2 : public Base1<T>, Base2<T> {
  using Base1<T>::Base1::Base1;
  using Base2<T>::Base2::Base2;
  Derived2();
};

int main()
{
  // PR c++/116276
Derived d;
Derived2 d2;
  return 0;
}
