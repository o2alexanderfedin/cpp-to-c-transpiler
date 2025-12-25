// Generated from: main.cpp
// Header file

struct Vector3D {
        float x;
        float y;
        float z;
};
void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other);
void Vector3D__ctor(struct Vector3D * this, float x, float y, float z);
Vector3D Vector3D_add(struct Vector3D * this, const Vector3D * other);
Vector3D Vector3D_subtract(struct Vector3D * this, const Vector3D * other);
float Vector3D_dot(struct Vector3D * this, const Vector3D * other);
Vector3D Vector3D_cross(struct Vector3D * this, const Vector3D * other);
float Vector3D_magnitude(struct Vector3D * this);
struct Matrix3x3 {
        float data[9];
};
void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other);
void Matrix3x3__ctor(struct Matrix3x3 * this);
void Matrix3x3__ctor_9(struct Matrix3x3 * this, float m00, float m01, float m02, float m10, float m11, float m12, float m20, float m21, float m22);
Matrix3x3 Matrix3x3_add(struct Matrix3x3 * this, const Matrix3x3 * other);
Matrix3x3 Matrix3x3_multiply(struct Matrix3x3 * this, const Matrix3x3 * other);
Vector3D Matrix3x3_multiply_Vector3D_ref(struct Matrix3x3 * this, const Vector3D * vec);
float Matrix3x3_get(struct Matrix3x3 * this, int row, int col);
void Matrix3x3_set(struct Matrix3x3 * this, int row, int col, float value);
int main();
