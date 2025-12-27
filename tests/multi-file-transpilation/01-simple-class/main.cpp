#include "Point.h"

int main() {
  Point p(3, 4);
  int dist = p.distanceSquared();  // Should be 25
  return dist == 25 ? 0 : 1;
}
