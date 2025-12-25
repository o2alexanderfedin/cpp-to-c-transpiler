// Generated from: main.cpp
// Implementation file

#include "main.cpp.h"

struct Vector3D {
        float x;
        float y;
        float z;
};
void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other) {
        this->x = other->x;
        this->y = other->y;
        this->z = other->z;
}


void Vector3D__ctor(struct Vector3D * this, float x, float y, float z) {
}


struct Vector3D Vector3D_add(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_subtract(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_dot(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_cross(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_magnitude(struct Vector3D * this);
struct Matrix3x3 {
        float data[9];
};
void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
        this->data = other->data;
}


void Matrix3x3__ctor(struct Matrix3x3 * this) {
}


void Matrix3x3__ctor_9(struct Matrix3x3 * this, float m00, float m01, float m02, float m10, float m11, float m12, float m20, float m21, float m22) {
}


struct Matrix3x3 Matrix3x3_add(struct Matrix3x3 * this, const struct Matrix3x3 * other);
struct Matrix3x3 Matrix3x3_multiply(struct Matrix3x3 * this, const struct Matrix3x3 * other);
struct Vector3D Matrix3x3_multiply_Vector3D_ref(struct Matrix3x3 * this, const struct Vector3D * vec);
float Matrix3x3_get(struct Matrix3x3 * this, int row, int col);
void Matrix3x3_set(struct Matrix3x3 * this, int row, int col, float value);
int main() {
        struct Vector3D v1;
        Vector3D__ctor(&v1, 1.F, 2.F, 3.F);
        struct Vector3D v2;
        Vector3D__ctor(&v2, 4.F, 5.F, 6.F);
        {
                struct Vector3D sum;
        }
        float dot = Vector3D_dot(&v1, v2);
        {
                struct Vector3D cross;
        }
        <recovery-expr>(printf, "Vector3D Tests:\n");
        <recovery-expr>(printf, "  v1 = (%.1f, %.1f, %.1f)\n", v1.x, v1.y, v1.z);
        <recovery-expr>(printf, "  v2 = (%.1f, %.1f, %.1f)\n", v2.x, v2.y, v2.z);
        <recovery-expr>(printf, "  v1 + v2 = (%.1f, %.1f, %.1f)\n", sum.x, sum.y, sum.z);
        <recovery-expr>(printf, "  v1 . v2 = %.1f\n", dot);
        <recovery-expr>(printf, "  v1 x v2 = (%.1f, %.1f, %.1f)\n", cross.x, cross.y, cross.z);
        struct Matrix3x3 m1;
        Matrix3x3__ctor_9(&m1, 1, 0, 0, 0, 1, 0, 0, 0, 1);
        struct Matrix3x3 m2;
        Matrix3x3__ctor_9(&m2, 2, 0, 0, 0, 2, 0, 0, 0, 2);
        {
                struct Matrix3x3 mProd;
        }
        {
                struct Vector3D transformed;
        }
        <recovery-expr>(printf, "\nMatrix3x3 Tests:\n");
        <recovery-expr>(printf, "  Identity * 2I = 2I (first element: %.1f)\n", mProd.get(0, 0));
        <recovery-expr>(printf, "  2I * v1 = (%.1f, %.1f, %.1f)\n", transformed.x, transformed.y, transformed.z);
        bool passed = true;
        passed = passed && (<recovery-expr>(fabsf, sum.x - 5.F) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, sum.y - 7.F) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, sum.z - 9.F) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, dot - 32.F) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, cross.x - (-3.F)) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, cross.y - 6.F) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, cross.z - (-3.F)) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, mProd.get(0, 0) - 2.F) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, transformed.x - 2.F) < 0.00100000005F);
        <recovery-expr>(printf, "\nValidation: %s\n", passed ? "PASS" : "FAIL");
        return passed ? 0 : 1;
}


