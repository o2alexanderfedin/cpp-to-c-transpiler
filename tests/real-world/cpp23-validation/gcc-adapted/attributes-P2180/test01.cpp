// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: attr-assume-opt.C
// Category: attributes
// Test ID: 01
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.


{
  [[assume (x == 2 && y < 3 && z < 20)]];
  unsigned q = x + y + z;
  if (q > 23)
    return 0;
  return 1;
}


{
  [[assume (x+12 == 14 && y >= 0 && y + 10 < 13 && z + 4 >= 4 && z - 2 < 18)]];
  unsigned q = x + y + z;
  if (q*2 > 46)
    return 0;
  return 1;
}

{
  [[assume (x + 12 == 14 && z / 2 > 0)]];
  [[assume (y >= 0 && z - 2 < 18)]];
  [[assume (y + 10 < 13 && z + 4 >= 2)]];
  int q = x + y + z;
  if (q * 2 > 46)
    return 0;
  if (z < 0)
    return 0;
  return 1;
}


void barn(int x);
bool assume_func (int x, int y, int z)
{
  if (z - 2 >= 18)
    return false;
  if (x+12 != 14)
    return false;
  barn (x);
  if (y < 0)
    return false;
  if (z + 4 < 4)
    return false;
  barn (y);
  if (y + 10 >= 13)
    return false;
  barn (z);
  return true;
}

{
  [[assume (assume_func (x, y, z))]];
  unsigned q = x + y + z;
  if (q*2 > 46)
    return 0;
  return 1;
}

int main()
{
  // P1774R8 - Portable assumptions
// Test the we can optimize based on conditions in assume.
int
f1 (unsigned x, unsigned y, unsigned z)
int
f2 (int x, int y, int z)
int
f3 (int x, int y, int z)
// This is the same as f2, except there is more complicated flow and 
// required a range-op update to bitwise or.
// assume (x+12 == 14 && y >= 0 && y + 10 < 13 && z + 4 >= 4 && z - 2 < 18)
// in different order and form with function calls to cause branches.
int
f2b (int x, int y, int z)
/*
/*
  return 0;
}
