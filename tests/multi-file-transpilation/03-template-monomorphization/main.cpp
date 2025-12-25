#include "Stack.h"

int main() {
  Stack<int> intStack;
  intStack.push(42);
  intStack.push(100);

  Stack<double> doubleStack;
  doubleStack.push(3.14);

  int i1 = intStack.pop();  // 100
  int i2 = intStack.pop();  // 42
  double d = doubleStack.pop();  // 3.14

  return (i1 == 100 && i2 == 42 && d > 3.0) ? 0 : 1;
}
