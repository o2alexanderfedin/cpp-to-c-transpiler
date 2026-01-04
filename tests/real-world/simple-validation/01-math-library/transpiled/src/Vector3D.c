#include "Vector3D.h"

struct Vector3D Vector3D__add__constVector3Dref(struct Vector3D * this, const struct Vector3D * other) {
	return (struct Vector3D){this->x + other.x, this->y + other.y, this->z + other.z};
;
}

struct Vector3D Vector3D__subtract__constVector3Dref(struct Vector3D * this, const struct Vector3D * other) {
	return (struct Vector3D){this->x - other.x, this->y - other.y, this->z - other.z};
;
}

float Vector3D__dot__constVector3Dref(struct Vector3D * this, const struct Vector3D * other) {
	return this->x * other.x + this->y * other.y + this->z * other.z;
;
}

struct Vector3D Vector3D__cross__constVector3Dref(struct Vector3D * this, const struct Vector3D * other) {
	return (struct Vector3D){this->y * other.z - this->z * other.y, this->z * other.x - this->x * other.z, this->x * other.y - this->y * other.x};
;
}

float Vector3D__magnitude__void(struct Vector3D * this) {
	return sqrtf(this->x * this->x + this->y * this->y + this->z * this->z);
;
}

