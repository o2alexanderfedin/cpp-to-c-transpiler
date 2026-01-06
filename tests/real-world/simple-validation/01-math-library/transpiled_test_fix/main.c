// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/01-math-library/./main.cpp
// Implementation file

#include "main.h"

float Vector3D_dot_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
int main() {
	Vector3D v1 = 1.F, 2.F, 3.F;
	Vector3D v2 = 4.F, 5.F, 6.F;
	Vector3D sum = Vector3D_add(&v1, v2);
	float dot = Vector3D_dot_const_Vector3D_ref(&v1, &v2);
	Vector3D cross = Vector3D_cross(&v1, v2);
	Matrix3x3 m1 = 1, 0, 0, 0, 1, 0, 0, 0, 1;
	Matrix3x3 m2 = 2, 0, 0, 0, 2, 0, 0, 0, 2;
	Matrix3x3 mProd = Matrix3x3_multiply(&m1, m2);
	Vector3D transformed = Matrix3x3_multiply(&m2, v1);
	bool passed = true;
	return passed ? 0 : 1;
;
}

