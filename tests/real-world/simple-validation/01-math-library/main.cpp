#include "Vector3D.h"
#include "Matrix3x3.h"
#include <cstdio>
#include <cmath>

int main() {
    // Test Vector3D operations
    Vector3D v1(1.0f, 2.0f, 3.0f);
    Vector3D v2(4.0f, 5.0f, 6.0f);

    Vector3D sum = v1.add(v2);
    float dot = v1.dot(v2);
    Vector3D cross = v1.cross(v2);

    printf("Vector3D Tests:\n");
    printf("  v1 = (%.1f, %.1f, %.1f)\n", v1.x, v1.y, v1.z);
    printf("  v2 = (%.1f, %.1f, %.1f)\n", v2.x, v2.y, v2.z);
    printf("  v1 + v2 = (%.1f, %.1f, %.1f)\n", sum.x, sum.y, sum.z);
    printf("  v1 . v2 = %.1f\n", dot);
    printf("  v1 x v2 = (%.1f, %.1f, %.1f)\n", cross.x, cross.y, cross.z);

    // Test Matrix3x3 operations
    Matrix3x3 m1(1, 0, 0,
                 0, 1, 0,
                 0, 0, 1);  // Identity matrix

    Matrix3x3 m2(2, 0, 0,
                 0, 2, 0,
                 0, 0, 2);  // 2 * Identity

    Matrix3x3 mProd = m1.multiply(m2);
    Vector3D transformed = m2.multiply(v1);

    printf("\nMatrix3x3 Tests:\n");
    printf("  Identity * 2I = 2I (first element: %.1f)\n", mProd.get(0, 0));
    printf("  2I * v1 = (%.1f, %.1f, %.1f)\n", transformed.x, transformed.y, transformed.z);

    // Validation
    bool passed = true;
    passed = passed && (fabsf(sum.x - 5.0f) < 0.001f);
    passed = passed && (fabsf(sum.y - 7.0f) < 0.001f);
    passed = passed && (fabsf(sum.z - 9.0f) < 0.001f);
    passed = passed && (fabsf(dot - 32.0f) < 0.001f);
    passed = passed && (fabsf(cross.x - (-3.0f)) < 0.001f);
    passed = passed && (fabsf(cross.y - 6.0f) < 0.001f);
    passed = passed && (fabsf(cross.z - (-3.0f)) < 0.001f);
    passed = passed && (fabsf(mProd.get(0, 0) - 2.0f) < 0.001f);
    passed = passed && (fabsf(transformed.x - 2.0f) < 0.001f);

    printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
    return passed ? 0 : 1;
}
