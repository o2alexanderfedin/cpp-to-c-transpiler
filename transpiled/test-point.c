// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./test-point.cpp
// Implementation file

#include "test-point.h"

static void Point__ctor_copy(struct Point * this, const struct Point * other) {
	this->x = other->x;
	this->y = other->y;
}

void Point__ctor(struct Point * this, int x, int y) {
	this->x = x;
	this->y = y;
}

int Point_getX(struct Point * this) {
	return this->x;
;
}

int Point_getY(struct Point * this) {
	return this->y;
;
}

