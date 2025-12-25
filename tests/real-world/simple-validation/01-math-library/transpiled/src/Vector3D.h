// Generated from: src/Vector3D.cpp
// Header file

struct Vector3D {
        float x;
        float y;
        float z;
};
void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other);
void Vector3D__ctor(struct Vector3D * this, float x, float y, float z);
struct Vector3D Vector3D_add(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_subtract(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_dot(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_cross(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_magnitude(struct Vector3D * this);
void Vector3D__ctor_3(struct Vector3D * this, float x, float y, float z);
struct Vector3D Vector3D_add_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_subtract_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_dot_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_cross_Vector3D_ref(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_magnitude(struct Vector3D * this);
