// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/class-basic.cpp
// Implementation file

#include "class-basic.h"

static void Point__ctor_copy(struct Point * this, const struct Point * other) {
	this->x = other->x;
	this->y = other->y;
}

int Point_getX(struct Point * this) {
	return this->x;
;
}

int Point_getY(struct Point * this) {
	return this->y;
;
}

void Point_setX_int(struct Point * this, int new_x) {
	this->x = new_x;
}

void Point_setY_int(struct Point * this, int new_y) {
	this->y = new_y;
}

int Point_distanceSquared(struct Point * this) {
	return this->x * this->x + this->y * this->y;
;
}

