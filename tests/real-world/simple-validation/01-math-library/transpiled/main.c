// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/01-math-library/main.cpp
// Implementation file

#include "main.h"

static void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other) {
	this->x = other->x;
	this->y = other->y;
	this->z = other->z;
}

static void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
	memcpy(&this->data, &other->data, sizeof this->data);
}

float Vector3D_dot(struct Vector3D * this, const struct Vector3D * other);
int main() {
	struct Vector3D v1;

	struct Vector3D v2;

	struct Vector3D sum;

	float dot = Vector3D_dot(&v1, &v2);

	struct Vector3D cross;

	struct Matrix3x3 m1;

	struct Matrix3x3 m2;

	struct Matrix3x3 mProd;

	struct Vector3D transformed;

	bool passed = true;

	return passed ? 0 : 1;
;
}

