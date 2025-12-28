// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/01-math-library/./src/Vector3D.cpp
// Header file

#pragma once

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
void Vector3D__ctor_3(struct Vector3D * this, float x, float y, float z);
struct Vector3D Vector3D_add_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_subtract_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_dot_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_cross_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_magnitude(struct Vector3D * this);
