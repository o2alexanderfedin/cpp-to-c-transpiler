// Generated from: main.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct Vector3D {
	float x;
	float y;
	float z;
};
static void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other);
struct Matrix3x3 {
	float data[9];
};
static void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other);
float Vector3D_dot(struct Vector3D * this, const struct Vector3D * other);
int main();
