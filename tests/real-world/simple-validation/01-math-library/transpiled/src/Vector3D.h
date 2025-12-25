// Generated from: src/Vector3D.cpp
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
static void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_add(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_subtract(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_dot(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_cross(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_magnitude(struct Vector3D * this);
void Vector3D__ctor(struct Vector3D * this, float x, float y, float z);
