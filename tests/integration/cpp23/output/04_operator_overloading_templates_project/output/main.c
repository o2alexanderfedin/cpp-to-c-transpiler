// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/04_operator_overloading_templates_project/main.cpp
// Implementation file

#include "main.h"

int main() {
	struct Vector2D_int v1;

	struct Vector2D_int v2;

	struct Vector2D_int v3;

	struct Vector2D_int v4;

	struct Vector2D_int v5;

	struct Vector2D_double vd1;

	struct Vector2D_double vd2;

	struct Vector2D_double vd3;

	return 0;
;
}

int Vector2D_int_getX(struct Vector2D_int * this) {
	return this->x;
;
}

int Vector2D_int_getY(struct Vector2D_int * this) {
	return this->y;
;
}

Vector2D<T> Vector2D_int_operator+(struct Vector2D_int * this, const Vector2D<T> * other) {
	return Vector2D<T>(this->x + other.x, this->y + other.y);
;
}

Vector2D<T> Vector2D_int_operator-(struct Vector2D_int * this, const Vector2D<T> * other) {
	return Vector2D<T>(this->x - other.x, this->y - other.y);
;
}

Vector2D<T> Vector2D_int_operator*(struct Vector2D_int * this, int scalar) {
	return Vector2D<T>(this->x * scalar, this->y * scalar);
;
}

bool Vector2D_int_operator==(struct Vector2D_int * this, const Vector2D<T> * other) {
	return this->x == other.x && this->y == other.y;
;
}

bool Vector2D_int_operator!=(struct Vector2D_int * this, const Vector2D<T> * other) {
	return !(*this == other);
;
}

int Vector2D_int_operator[](struct Vector2D_int * this, int index) {
	return index == 0 ? this->x : this->y;
;
}

double Vector2D_double_getX(struct Vector2D_double * this) {
	return this->x;
;
}

double Vector2D_double_getY(struct Vector2D_double * this) {
	return this->y;
;
}

Vector2D<T> Vector2D_double_operator+(struct Vector2D_double * this, const Vector2D<T> * other) {
	return Vector2D<T>(this->x + other.x, this->y + other.y);
;
}

Vector2D<T> Vector2D_double_operator-(struct Vector2D_double * this, const Vector2D<T> * other) {
	return Vector2D<T>(this->x - other.x, this->y - other.y);
;
}

Vector2D<T> Vector2D_double_operator*(struct Vector2D_double * this, double scalar) {
	return Vector2D<T>(this->x * scalar, this->y * scalar);
;
}

bool Vector2D_double_operator==(struct Vector2D_double * this, const Vector2D<T> * other) {
	return this->x == other.x && this->y == other.y;
;
}

bool Vector2D_double_operator!=(struct Vector2D_double * this, const Vector2D<T> * other) {
	return !(*this == other);
;
}

double Vector2D_double_operator[](struct Vector2D_double * this, int index) {
	return index == 0 ? this->x : this->y;
;
}

