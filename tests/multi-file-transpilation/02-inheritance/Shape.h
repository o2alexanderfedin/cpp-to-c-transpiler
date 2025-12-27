#ifndef SHAPE_H
#define SHAPE_H

class Shape {
public:
  virtual ~Shape() {}
  virtual int area() const = 0;  // Pure virtual

  int getID() const { return m_id; }
  void setID(int id) { m_id = id; }

protected:
  int m_id = 0;
};

#endif // SHAPE_H
