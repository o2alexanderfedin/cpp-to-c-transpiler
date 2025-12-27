#ifndef MATRIX3X3_H
#define MATRIX3X3_H

#include "Vector3D.h"

class Matrix3x3 {
private:
    float data[9];  // Row-major order

public:
    Matrix3x3();
    Matrix3x3(float m00, float m01, float m02,
              float m10, float m11, float m12,
              float m20, float m21, float m22);

    Matrix3x3 add(const Matrix3x3& other) const;
    Matrix3x3 multiply(const Matrix3x3& other) const;
    Vector3D multiply(const Vector3D& vec) const;
    float get(int row, int col) const;
    void set(int row, int col, float value);
};

#endif // MATRIX3X3_H
