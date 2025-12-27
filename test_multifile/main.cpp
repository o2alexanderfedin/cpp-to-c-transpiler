#include "Rectangle.h"

int main() {
    Point p1(0, 0);
    Point p2(10, 20);
    Rectangle rect(p1, p2);
    return rect.getArea();
}
