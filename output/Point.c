// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/multi-file-transpilation/01-simple-class/Point.cpp
// Implementation file

#include "Point.h"

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

int Point_getY(struct Point *this) {
        return this->m_y;
}

void Point_setX(struct Point *this, int x) {
        this->m_x = x;
}

void Point_setY(struct Point *this, int y) {
        this->m_y = y;
}

int Point_distanceSquared(struct Point *this) {
        return this->m_x * this->m_x + this->m_y * this->m_y;
}

void Point__ctor_2(struct Point *this, int x, int y) {
        this->m_x = x;
        this->m_y = y;
}

int Point_getY(struct Point *this) {
        return this->m_y;
}

void Point_setX_int(struct Point *this, int x) {
        this->m_x = x;
}

void Point_setY_int(struct Point *this, int y) {
        this->m_y = y;
}

int Point_distanceSquared(struct Point *this) {
        return this->m_x * this->m_x + this->m_y * this->m_y;
}

