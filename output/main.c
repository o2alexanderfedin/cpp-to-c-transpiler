// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/multi-file-transpilation/01-simple-class/main.cpp
// Implementation file

#include "main.h"

struct Point {
        int m_x;
        int m_y;
};
void Point__ctor_copy(struct Point *this, const struct Point *other) {
        this->m_x = other->m_x;
        this->m_y = other->m_y;
}

void Point__ctor(struct Point *this, int x, int y) {
}

int Point_getX(struct Point *this) {
        return this->m_x;
}

int Point_getY(struct Point *this);
void Point_setX(struct Point *this, int x);
void Point_setY(struct Point *this, int y);
int Point_distanceSquared(struct Point *this);
int main() {
        struct Point p;
        Point__ctor(&p, 3, 4);
        int dist = Point_distanceSquared(&p);
        return dist == 25 ? 0 : 1;
}

