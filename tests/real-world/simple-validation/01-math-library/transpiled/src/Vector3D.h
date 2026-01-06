#pragma once

struct Vector3D {
	float x;
	float y;
	float z;
};
struct Vector3D Vector3D__add__constclassVector3Dref(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D__subtract__constclassVector3Dref(struct Vector3D * this, const struct Vector3D * other);
float Vector3D__dot__constclassVector3Dref(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D__cross__constclassVector3Dref(struct Vector3D * this, const struct Vector3D * other);
float Vector3D__magnitude__void(struct Vector3D * this);
