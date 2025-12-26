// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/01-math-library/src/Vector3D.cpp
// Implementation file

#include "Vector3D.h"

static void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other) {
	this->x = other->x;
	this->y = other->y;
	this->z = other->z;
}

struct Vector3D Vector3D_add(struct Vector3D * this, const struct Vector3D * other) {
	return (struct Vector3D){this->x + other->x, this->y + other->y, this->z + other->z};
;
}

struct Vector3D Vector3D_subtract(struct Vector3D * this, const struct Vector3D * other) {
	return (struct Vector3D){this->x - other->x, this->y - other->y, this->z - other->z};
;
}

float Vector3D_dot(struct Vector3D * this, const struct Vector3D * other) {
	return this->x * other->x + this->y * other->y + this->z * other->z;
;
}

struct Vector3D Vector3D_cross(struct Vector3D * this, const struct Vector3D * other) {
	return (struct Vector3D){this->y * other->z - this->z * other->y, this->z * other->x - this->x * other->z, this->x * other->y - this->y * other->x};
;
}

float Vector3D_magnitude(struct Vector3D * this) {
}

void Vector3D__ctor(struct Vector3D * this, float x, float y, float z) {
	this->x = x;
	this->y = y;
	this->z = z;
}

