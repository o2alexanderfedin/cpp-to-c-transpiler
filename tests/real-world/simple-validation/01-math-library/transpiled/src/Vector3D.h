#pragma once

struct Vector3D {
	float x;
	float y;
	float z;
};
struct Vector3D Vector3D__add__constVector3Dref(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D__subtract__constVector3Dref(struct Vector3D * this, const struct Vector3D * other);
float Vector3D__dot__constVector3Dref(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D__cross__constVector3Dref(struct Vector3D * this, const struct Vector3D * other);
float Vector3D__magnitude__void(struct Vector3D * this);
