// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/01-math-library/./src/Matrix3x3.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/Vector3D.h"

static void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other);
struct Matrix3x3 {
	float data[9];
};
static void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other);
void Matrix3x3__ctor_0(struct Matrix3x3 * this);
void Matrix3x3__ctor_9(struct Matrix3x3 * this, float m00, float m01, float m02, float m10, float m11, float m12, float m20, float m21, float m22);
struct Matrix3x3 Matrix3x3_add_const_Matrix3x3_ref(struct Matrix3x3 * this, const struct Matrix3x3 * other);
struct Matrix3x3 Matrix3x3_multiply_const_Matrix3x3_ref(struct Matrix3x3 * this, const struct Matrix3x3 * other);
struct Vector3D Matrix3x3_multiply_const_Vector3D_ref(struct Matrix3x3 * this, const struct Vector3D * vec);
float Matrix3x3_get_int_int(struct Matrix3x3 * this, int row, int col);
void Matrix3x3_set_int_int_float(struct Matrix3x3 * this, int row, int col, float value);
