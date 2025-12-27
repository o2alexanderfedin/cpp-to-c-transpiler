// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/class-basic.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct Point {
	int x;
	int y;
};
static void Point__ctor_copy(struct Point * this, const struct Point * other);
void Point__ctor(struct Point * this, int x_val, int y_val);
int Point_getX(struct Point * this);
int Point_getY(struct Point * this);
void Point_setX(struct Point * this, int new_x);
void Point_setY(struct Point * this, int new_y);
int Point_distanceSquared(struct Point * this);
