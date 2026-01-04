#include "Matrix3x3.h"

struct Matrix3x3 Matrix3x3__add__constMatrix3x3ref(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
	struct Matrix3x3 result = (struct Matrix3x3){};
	for (int i = 0; i < 9; i++) {
        result.data[i] = this->data[i] + other.data[i];
}

	return (struct Matrix3x3){result};
;
}

struct Matrix3x3 Matrix3x3__multiply__constMatrix3x3ref(struct Matrix3x3 * this, const struct Matrix3x3 * other) {
	struct Matrix3x3 result = (struct Matrix3x3){};
	for (int row = 0; row < 3; row++) {
        for (int col = 0; col < 3; col++) {
                float sum = 0.F;
                for (int k = 0; k < 3; k++) {
                }
                result.data[row * 3 + col] = sum;
        }
}

	return (struct Matrix3x3){result};
;
}

struct Vector3D Matrix3x3__multiply__constVector3Dref(struct Matrix3x3 * this, const struct Vector3D * vec) {
	return (Vector3D){this->data[0] * vec.x + this->data[1] * vec.y + this->data[2] * vec.z, this->data[3] * vec.x + this->data[4] * vec.y + this->data[5] * vec.z, this->data[6] * vec.x + this->data[7] * vec.y + this->data[8] * vec.z};
;
}

float Matrix3x3__get__int_int(struct Matrix3x3 * this, int row, int col) {
	return this->data[row * 3 + col];
;
}

void Matrix3x3__set__int_int_float(struct Matrix3x3 * this, int row, int col, float value) {
	this->data[row * 3 + col] = value;
}

