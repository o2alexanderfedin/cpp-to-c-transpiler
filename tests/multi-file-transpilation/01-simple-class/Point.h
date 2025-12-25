#ifndef POINT_H
#define POINT_H

class Point {
public:
  Point(int x, int y);

  // Inline method - must be in header
  int getX() const { return m_x; }

  int getY() const;  // Declaration only
  void setX(int x);
  void setY(int y);

  int distanceSquared() const;

private:
  int m_x;
  int m_y;
};

#endif // POINT_H
