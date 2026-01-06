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
	printf("Vector3D Tests:\n");
	printf("  v1 = (%.1f, %.1f, %.1f)\n", v1.x, v1.y, v1.z);
	printf("  v2 = (%.1f, %.1f, %.1f)\n", v2.x, v2.y, v2.z);
	printf("  v1 + v2 = (%.1f, %.1f, %.1f)\n", sum.x, sum.y, sum.z);
	printf("  v1 . v2 = %.1f\n", dot);
	printf("  v1 x v2 = (%.1f, %.1f, %.1f)\n", cross.x, cross.y, cross.z);
	struct Matrix3x3 m1;
	Matrix3x3__ctor_9(&m1, 1, 0, 0, 0, 1, 0, 0, 0, 1);
	struct Matrix3x3 m2;
	Matrix3x3__ctor_9(&m2, 2, 0, 0, 0, 2, 0, 0, 0, 2);
	struct Matrix3x3 mProd;
	mProd = Matrix3x3_multiply_const_Matrix3x3_ref(&m1, &m2);
	struct Vector3D transformed;
	transformed = Matrix3x3_multiply_const_Vector3D_ref(&m2, &v1);
	printf("\nMatrix3x3 Tests:\n");
	printf("  Identity * 2I = 2I (first element: %.1f)\n", Matrix3x3_get_int_int(&mProd, 0, 0));
	printf("  2I * v1 = (%.1f, %.1f, %.1f)\n", transformed.x, transformed.y, transformed.z);
	bool passed = true;
	passed = passed && (fabsf(sum.x - 5.F) < 0.00100000005F);
	passed = passed && (fabsf(sum.y - 7.F) < 0.00100000005F);
	passed = passed && (fabsf(sum.z - 9.F) < 0.00100000005F);
	passed = passed && (fabsf(dot - 32.F) < 0.00100000005F);
	passed = passed && (fabsf(cross.x - (-3.F)) < 0.00100000005F);
	passed = passed && (fabsf(cross.y - 6.F) < 0.00100000005F);
	passed = passed && (fabsf(cross.z - (-3.F)) < 0.00100000005F);
	passed = passed && (fabsf(Matrix3x3_get_int_int(&mProd, 0, 0) - 2.F) < 0.00100000005F);
	passed = passed && (fabsf(transformed.x - 2.F) < 0.00100000005F);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
}

