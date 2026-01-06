#pragma once

struct Matrix3x3 {
	float data[9];
};
struct Matrix3x3 Matrix3x3__add__constclassMatrix3x3ref(struct Matrix3x3 * this, const struct Matrix3x3 * other);
struct Matrix3x3 Matrix3x3__multiply__constclassMatrix3x3ref(struct Matrix3x3 * this, const struct Matrix3x3 * other);
struct Vector3D Matrix3x3__multiply__constclassVector3Dref(struct Matrix3x3 * this, const struct Vector3D * vec);
float Matrix3x3__get__int_int(struct Matrix3x3 * this, int row, int col);
void Matrix3x3__set__int_int_float(struct Matrix3x3 * this, int row, int col, float value);
