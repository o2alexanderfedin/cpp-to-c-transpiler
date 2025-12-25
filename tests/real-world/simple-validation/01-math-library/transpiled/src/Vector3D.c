// Generated from: src/Vector3D.cpp
// Implementation file

#include "Vector3D.h"

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


struct Vector3D Vector3D_add(struct Vector3D * this, const struct Vector3D * other) {
        return Vector3D(this->x + other.x, this->y + other.y, this->z + other.z);
}


struct Vector3D Vector3D_subtract(struct Vector3D * this, const struct Vector3D * other) {
        return Vector3D(this->x - other.x, this->y - other.y, this->z - other.z);
}


float Vector3D_dot(struct Vector3D * this, const struct Vector3D * other) {
        return this->x * other.x + this->y * other.y + this->z * other.z;
}


struct Vector3D Vector3D_cross(struct Vector3D * this, const struct Vector3D * other) {
        return Vector3D(this->y * other.z - this->z * other.y, this->z * other.x - this->x * other.z, this->x * other.y - this->y * other.x);
}


float Vector3D_magnitude(struct Vector3D * this) {
        return <recovery-expr>(sqrtf, this->x * this->x + this->y * this->y + this->z * this->z);
}


void Vector3D__ctor_3(struct Vector3D * this, float x, float y, float z) {
        this->x = x;
        this->y = y;
        this->z = z;
}


struct Vector3D Vector3D_add_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other) {
        return Vector3D(this->x + other.x, this->y + other.y, this->z + other.z);
}


struct Vector3D Vector3D_subtract_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other) {
        return Vector3D(this->x - other.x, this->y - other.y, this->z - other.z);
}


float Vector3D_dot_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other) {
        return this->x * other.x + this->y * other.y + this->z * other.z;
}


struct Vector3D Vector3D_cross_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other) {
        return Vector3D(this->y * other.z - this->z * other.y, this->z * other.x - this->x * other.z, this->x * other.y - this->y * other.x);
}


float Vector3D_magnitude(struct Vector3D * this) {
        return <recovery-expr>(sqrtf, this->x * this->x + this->y * this->y + this->z * this->z);
}


