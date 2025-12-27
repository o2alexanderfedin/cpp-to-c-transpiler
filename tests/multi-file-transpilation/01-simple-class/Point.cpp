#include "Point.h"

Point::Point(int x, int y) : m_x(x), m_y(y) {}

int Point::getY() const { return m_y; }

void Point::setX(int x) { m_x = x; }

void Point::setY(int y) { m_y = y; }

int Point::distanceSquared() const {
  return m_x * m_x + m_y * m_y;
}
