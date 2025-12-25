#ifndef VECTOR3D_H
#define VECTOR3D_H

class Vector3D {
public:
    float x, y, z;

    Vector3D(float x, float y, float z);
    Vector3D add(const Vector3D& other) const;
    Vector3D subtract(const Vector3D& other) const;
    float dot(const Vector3D& other) const;
    Vector3D cross(const Vector3D& other) const;
    float magnitude() const;
};

#endif // VECTOR3D_H
