#ifndef RECTANGLE_H
#define RECTANGLE_H

#include "Shape.h"

// Header-only class (common in modern C++)
class Rectangle : public Shape {
public:
  Rectangle(int w, int h) : m_width(w), m_height(h) {}

  int area() const override {
    return m_width * m_height;
  }

  int getWidth() const { return m_width; }
  int getHeight() const { return m_height; }

private:
  int m_width;
  int m_height;
};

#endif // RECTANGLE_H
