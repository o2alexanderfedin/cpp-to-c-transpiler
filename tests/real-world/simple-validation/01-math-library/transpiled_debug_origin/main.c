// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/01-math-library/./main.cpp
// Implementation file

#include "main.h"

static void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other) {
	this->x = other->x;
	this->y = other->y;
	this->z = other->z;
}

static void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
	memcpy(&this->data, &other->data, sizeof(float[9]));
}

int main() {
	struct Vector3D v1;
	Vector3D__ctor_3(&v1, 1.F, 2.F, 3.F);
	struct Vector3D v2;
	Vector3D__ctor_3(&v2, 4.F, 5.F, 6.F);
	struct Vector3D sum;
	sum = Vector3D_add_const_Vector3D_ref(&v1, &v2);
	float dot = Vector3D_dot_const_Vector3D_ref(&v1, &v2);
	struct Vector3D cross;
	cross = Vector3D_cross_const_Vector3D_ref(&v1, &v2);
	struct Matrix3x3 m1;
	Matrix3x3__ctor_9(&m1, 1, 0, 0, 0, 1, 0, 0, 0, 1);
	struct Matrix3x3 m2;
	Matrix3x3__ctor_9(&m2, 2, 0, 0, 0, 2, 0, 0, 0, 2);
	struct Matrix3x3 mProd;
	mProd = Matrix3x3_multiply_const_Matrix3x3_ref(&m1, &m2);
	struct Vector3D transformed;
	transformed = Matrix3x3_multiply_const_Vector3D_ref(&m2, &v1);
	bool passed = true;
	return passed ? 0 : 1;
;
}

