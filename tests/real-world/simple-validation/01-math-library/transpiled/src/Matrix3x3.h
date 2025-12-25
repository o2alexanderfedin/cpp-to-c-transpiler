// Generated from: src/Matrix3x3.cpp
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
struct Matrix3x3 Matrix3x3_add(struct Matrix3x3 * this, const struct Matrix3x3 * other);
struct Matrix3x3 Matrix3x3_multiply(struct Matrix3x3 * this, const struct Matrix3x3 * other);
struct Vector3D Matrix3x3_multiply_Vector3D_ref(struct Matrix3x3 * this, const struct Vector3D * vec);
float Matrix3x3_get(struct Matrix3x3 * this, int row, int col);
void Matrix3x3_set(struct Matrix3x3 * this, int row, int col, float value);
void Matrix3x3__ctor(struct Matrix3x3 * this);
void Matrix3x3__ctor_9(struct Matrix3x3 * this, float m00, float m01, float m02, float m10, float m11, float m12, float m20, float m21, float m22);
