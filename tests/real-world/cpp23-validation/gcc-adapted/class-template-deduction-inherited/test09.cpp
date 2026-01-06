// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: class-deduction-inherited8.C
// Category: class-template-deduction
// Test ID: 09
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


template <typename> class QFlagsStorage{};

template <typename Enum> struct QFlagsStorageHelper : QFlagsStorage<Enum>  {
  using QFlagsStorage<Enum>::QFlagsStorage;
public:
  QFlagsStorageHelper(Enum);
};

template <typename Enum> struct QFlags : public QFlagsStorageHelper<Enum> {
  using Base = QFlagsStorageHelper<Enum>;
  using Base::Base;
  QFlags(Enum);
};

void f(int flag) {
  QFlags{int{}};
}

int main()
{
  // PR c++/119687
  return 0;
}
