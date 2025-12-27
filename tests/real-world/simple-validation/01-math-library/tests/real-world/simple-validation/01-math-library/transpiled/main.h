// Generated from: main.cpp
// Header file

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
void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other);
void Vector3D__ctor(struct Vector3D * this, float x, float y, float z);
struct Matrix3x3 {
        float data[9];
};
void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other);
void Matrix3x3__ctor(struct Matrix3x3 * this);
void Matrix3x3__ctor_9(struct Matrix3x3 * this, float m00, float m01, float m02, float m10, float m11, float m12, float m20, float m21, float m22);
int main();
