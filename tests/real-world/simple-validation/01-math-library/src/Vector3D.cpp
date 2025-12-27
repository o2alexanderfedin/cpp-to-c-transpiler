#include "Vector3D.h"
#include <cmath>

Vector3D::Vector3D(float x, float y, float z) : x(x), y(y), z(z) {}

Vector3D Vector3D::add(const Vector3D& other) const {
    return Vector3D(x + other.x, y + other.y, z + other.z);
}

Vector3D Vector3D::subtract(const Vector3D& other) const {
    return Vector3D(x - other.x, y - other.y, z - other.z);
}

float Vector3D::dot(const Vector3D& other) const {
    return x * other.x + y * other.y + z * other.z;
}

Vector3D Vector3D::cross(const Vector3D& other) const {
    return Vector3D(
        y * other.z - z * other.y,
        z * other.x - x * other.z,
        x * other.y - y * other.x
    );
}

float Vector3D::magnitude() const {
    return sqrtf(x * x + y * y + z * z);
}
