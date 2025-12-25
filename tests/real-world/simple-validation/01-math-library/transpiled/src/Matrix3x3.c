// Generated from: src/Matrix3x3.cpp
// Implementation file

#include "Matrix3x3.h"

void Vector3D__ctor_copy(struct Vector3D * this, const struct Vector3D * other) {
        this->x = other->x;
        this->y = other->y;
        this->z = other->z;
}


void Vector3D__ctor(struct Vector3D * this, float x, float y, float z) {
}


struct Vector3D Vector3D_add(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_subtract(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_dot(struct Vector3D * this, const struct Vector3D * other);
struct Vector3D Vector3D_cross(struct Vector3D * this, const struct Vector3D * other);
float Vector3D_magnitude(struct Vector3D * this);
void Matrix3x3__ctor_copy(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
        this->data = other->data;
}


void Matrix3x3__ctor(struct Matrix3x3 * this) {
        for (int i = 0; i < 9; i++) {
                this->data[i] = 0.F;
        }
}


void Matrix3x3__ctor_9(struct Matrix3x3 * this, float m00, float m01, float m02, float m10, float m11, float m12, float m20, float m21, float m22) {
        this->data[0] = m00;
        this->data[1] = m01;
        this->data[2] = m02;
        this->data[3] = m10;
        this->data[4] = m11;
        this->data[5] = m12;
        this->data[6] = m20;
        this->data[7] = m21;
        this->data[8] = m22;
}


struct Matrix3x3 Matrix3x3_add(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
        {
                struct Matrix3x3 result;
        }
        for (int i = 0; i < 9; i++) {
                result.data[i] = this->data[i] + other.data[i];
        }
        return result;
}


struct Matrix3x3 Matrix3x3_multiply(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
        {
                struct Matrix3x3 result;
        }
        for (int row = 0; row < 3; row++) {
                for (int col = 0; col < 3; col++) {
                        float sum = 0.F;
                        for (int k = 0; k < 3; k++) {
                                sum += this->data[row * 3 + k] * other.data[k * 3 + col];
                        }
                        result.data[row * 3 + col] = sum;
                }
        }
        return result;
}


struct Vector3D Matrix3x3_multiply_Vector3D_ref(struct Matrix3x3 * this, const struct Vector3D * vec) {
        return this->data[0] * vec->x + this->data[1] * vec->y + this->data[2] * vec->z, this->data[3] * vec->x + this->data[4] * vec->y + this->data[5] * vec->z, this->data[6] * vec->x + this->data[7] * vec->y + this->data[8] * vec->z;
}


float Matrix3x3_get(struct Matrix3x3 * this, int row, int col) {
        return this->data[row * 3 + col];
}


void Matrix3x3_set(struct Matrix3x3 * this, int row, int col, float value) {
        this->data[row * 3 + col] = value;
}


void Matrix3x3__ctor_0(struct Matrix3x3 * this) {
        for (int i = 0; i < 9; i++) {
                this->data[i] = 0.F;
        }
}


void Matrix3x3__ctor_9(struct Matrix3x3 * this, float m00, float m01, float m02, float m10, float m11, float m12, float m20, float m21, float m22) {
        this->data[0] = m00;
        this->data[1] = m01;
        this->data[2] = m02;
        this->data[3] = m10;
        this->data[4] = m11;
        this->data[5] = m12;
        this->data[6] = m20;
        this->data[7] = m21;
        this->data[8] = m22;
}


struct Matrix3x3 Matrix3x3_add_Matrix3x3_ref(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
        struct Matrix3x3 result;
        Matrix3x3__ctor_0(&result);
        for (int i = 0; i < 9; i++) {
                result.data[i] = this->data[i] + other.data[i];
        }
        return result;
}


struct Matrix3x3 Matrix3x3_multiply_Matrix3x3_ref(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
        struct Matrix3x3 result;
        Matrix3x3__ctor_0(&result);
        for (int row = 0; row < 3; row++) {
                for (int col = 0; col < 3; col++) {
                        float sum = 0.F;
                        for (int k = 0; k < 3; k++) {
                                sum += this->data[row * 3 + k] * other.data[k * 3 + col];
                        }
                        result.data[row * 3 + col] = sum;
                }
        }
        return result;
}


struct Vector3D Matrix3x3_multiply_Vector3D_ref(struct Matrix3x3 * this, const struct Vector3D * vec) {
        return this->data[0] * vec->x + this->data[1] * vec->y + this->data[2] * vec->z, this->data[3] * vec->x + this->data[4] * vec->y + this->data[5] * vec->z, this->data[6] * vec->x + this->data[7] * vec->y + this->data[8] * vec->z;
}


float Matrix3x3_get_int_int(struct Matrix3x3 * this, int row, int col) {
        return this->data[row * 3 + col];
}


void Matrix3x3_set_int_int_float(struct Matrix3x3 * this, int row, int col, float value) {
        this->data[row * 3 + col] = value;
}


