// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/01-math-library/./src/Vector3D.cpp
// Implementation file

#include "Vector3D.h"

static void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other) {
	this->x = other->x;
	this->y = other->y;
	this->z = other->z;
}

void Vector3D__ctor_3(struct Vector3D * this, float x, float y, float z) {
	this->x = x;
	this->y = y;
	this->z = z;
}

extern struct Vector3D Vector3D_add_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other) {
	{
		struct Vector3D __return_temp;
		Vector3D__ctor_3(&__return_temp, this->x + other->x, this->y + other->y, this->z + other->z);
		return __return_temp;
;
	}
}

extern struct Vector3D Vector3D_subtract_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other) {
	{
		struct Vector3D __return_temp;
		Vector3D__ctor_3(&__return_temp, this->x - other->x, this->y - other->y, this->z - other->z);
		return __return_temp;
;
	}
}

extern float Vector3D_dot_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other) {
	return this->x * other->x + this->y * other->y + this->z * other->z;
;
}

extern struct Vector3D Vector3D_cross_const_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other) {
	{
		struct Vector3D __return_temp;
		Vector3D__ctor_3(&__return_temp, this->y * other->z - this->z * other->y, this->z * other->x - this->x * other->z, this->x * other->y - this->y * other->x);
		return __return_temp;
;
	}
}

extern float Vector3D_magnitude(struct Vector3D * this) {
}

