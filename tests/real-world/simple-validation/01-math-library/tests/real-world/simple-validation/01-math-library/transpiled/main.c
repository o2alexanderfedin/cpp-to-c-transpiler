// Generated from: main.cpp
// Implementation file

#include "main.h"

void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other) {
        this->x = other->x;
        this->y = other->y;
        this->z = other->z;
}


void Vector3D__ctor(struct Vector3D * this, float x, float y, float z) {
}


void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
        memcpy(&this->data, &other->data, sizeof this->data);
}


void Matrix3x3__ctor(struct Matrix3x3 * this) {
}


void Matrix3x3__ctor_9(struct Matrix3x3 * this, float m00, float m01, float m02, float m10, float m11, float m12, float m20, float m21, float m22) {
}


int main() {
        struct Vector3D v1;
        Vector3D__ctor(&v1, 1.F, 2.F, 3.F);
        struct Vector3D v2;
        Vector3D__ctor(&v2, 4.F, 5.F, 6.F);
        struct Vector3D sum;
        float dot = Vector3D_dot(&v1, &v2);
        struct Vector3D cross;
        struct Matrix3x3 m1;
        Matrix3x3__ctor_9(&m1, 1, 0, 0, 0, 1, 0, 0, 0, 1);
        struct Matrix3x3 m2;
        Matrix3x3__ctor_9(&m2, 2, 0, 0, 0, 2, 0, 0, 0, 2);
        struct Matrix3x3 mProd;
        struct Vector3D transformed;
        bool passed = true;
        return passed ? 0 : 1;
}


