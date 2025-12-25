#include "Rectangle.h"

int main() {
  Rectangle rect(5, 10);
  int a = rect.area();  // Should be 50
  return a == 50 ? 0 : 1;
}
