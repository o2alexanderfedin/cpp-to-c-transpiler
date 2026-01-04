#include "main.h"

int main() {
	struct Vector3D v1 = (struct Vector3D){1.F, 2.F, 3.F};
	struct Vector3D v2 = (struct Vector3D){4.F, 5.F, 6.F};
	struct Vector3D sum = Vector3D_add(&v1, &v2);
	float dot = Vector3D_dot(&v1, &v2);
	struct Vector3D cross = Vector3D_cross(&v1, &v2);
	printf("Vector3D Tests:\n");
	printf("  v1 = (%.1f, %.1f, %.1f)\n", v1.x, v1.y, v1.z);
	printf("  v2 = (%.1f, %.1f, %.1f)\n", v2.x, v2.y, v2.z);
	printf("  v1 + v2 = (%.1f, %.1f, %.1f)\n", sum.x, sum.y, sum.z);
	printf("  v1 . v2 = %.1f\n", dot);
	printf("  v1 x v2 = (%.1f, %.1f, %.1f)\n", cross.x, cross.y, cross.z);
	struct Matrix3x3 m1 = (struct Matrix3x3){1, 0, 0, 0, 1, 0, 0, 0, 1};
	struct Matrix3x3 m2 = (struct Matrix3x3){2, 0, 0, 0, 2, 0, 0, 0, 2};
	struct Matrix3x3 mProd = Matrix3x3_multiply(&m1, &m2);
	struct Vector3D transformed = Matrix3x3_multiply(&m2, &v1);
	printf("\nMatrix3x3 Tests:\n");
	printf("  Identity * 2I = 2I (first element: %.1f)\n", get(&mProd, 0, 0));
	printf("  2I * v1 = (%.1f, %.1f, %.1f)\n", transformed.x, transformed.y, transformed.z);
	bool passed = 1;
	passed = passed && (fabsf(sum.x - 5.F) < 0.00100000005F);
	passed = passed && (fabsf(sum.y - 7.F) < 0.00100000005F);
	passed = passed && (fabsf(sum.z - 9.F) < 0.00100000005F);
	passed = passed && (fabsf(dot - 32.F) < 0.00100000005F);
	passed = passed && (fabsf(cross.x - (-3.F)) < 0.00100000005F);
	passed = passed && (fabsf(cross.y - 6.F) < 0.00100000005F);
	passed = passed && (fabsf(cross.z - (-3.F)) < 0.00100000005F);
	passed = passed && (fabsf(get(&mProd, 0, 0) - 2.F) < 0.00100000005F);
	passed = passed && (fabsf(transformed.x - 2.F) < 0.00100000005F);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
}

