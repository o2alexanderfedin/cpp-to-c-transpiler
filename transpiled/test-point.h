// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./test-point.cpp
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
void Point__ctor(struct Point * this, int x, int y);
int Point_getX(struct Point * this);
int Point_getY(struct Point * this);
