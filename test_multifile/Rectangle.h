#pragma once
#include "Point.h"

class Rectangle {
private:
    Point topLeft;
    Point bottomRight;

public:
    Rectangle(const Point& tl, const Point& br);
    int getArea() const;
    int getWidth() const;
    int getHeight() const;
};
