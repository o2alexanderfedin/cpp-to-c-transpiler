// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/multi-file-transpilation/01-simple-class/main.cpp
// Header file

struct Point {
        int m_x;
        int m_y;
};
void Point__ctor_copy(struct Point * this, const struct Point * other);
void Point__ctor(struct Point * this, int x, int y);
int Point_getX(struct Point * this);
int Point_getY(struct Point * this);
void Point_setX(struct Point * this, int x);
void Point_setY(struct Point * this, int y);
int Point_distanceSquared(struct Point * this);
int main();
