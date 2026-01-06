#include "Matrix3x3.h"

Matrix3x3::Matrix3x3() {
    for (int i = 0; i < 9; i++) {
        data[i] = 0.0f;
    }
}

Matrix3x3::Matrix3x3(float m00, float m01, float m02,
                     float m10, float m11, float m12,
                     float m20, float m21, float m22) {
    data[0] = m00; data[1] = m01; data[2] = m02;
    data[3] = m10; data[4] = m11; data[5] = m12;
    data[6] = m20; data[7] = m21; data[8] = m22;
}

Matrix3x3 Matrix3x3::add(const Matrix3x3& other) const {
    Matrix3x3 result;
    for (int i = 0; i < 9; i++) {
        result.data[i] = data[i] + other.data[i];
    }
    return result;
}

Matrix3x3 Matrix3x3::multiply(const Matrix3x3& other) const {
    Matrix3x3 result;
    for (int row = 0; row < 3; row++) {
        for (int col = 0; col < 3; col++) {
            float sum = 0.0f;
            for (int k = 0; k < 3; k++) {
                sum += data[row * 3 + k] * other.data[k * 3 + col];
            }
            result.data[row * 3 + col] = sum;
        }
    }
    return result;
}

Vector3D Matrix3x3::multiply(const Vector3D& vec) const {
    return Vector3D(
        data[0] * vec.x + data[1] * vec.y + data[2] * vec.z,
        data[3] * vec.x + data[4] * vec.y + data[5] * vec.z,
        data[6] * vec.x + data[7] * vec.y + data[8] * vec.z
    );
}

float Matrix3x3::get(int row, int col) const {
    return data[row * 3 + col];
}

void Matrix3x3::set(int row, int col, float value) {
    data[row * 3 + col] = value;
}
