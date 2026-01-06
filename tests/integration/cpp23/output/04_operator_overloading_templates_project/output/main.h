// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/04_operator_overloading_templates_project/main.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

int main();
struct Vector2D_int {
	int x;
	int y;
};
int Vector2D_int_getX(struct Vector2D_int * this);
int Vector2D_int_getY(struct Vector2D_int * this);
Vector2D<T> Vector2D_int_operator+(struct Vector2D_int * this, const Vector2D<T> * other);
Vector2D<T> Vector2D_int_operator-(struct Vector2D_int * this, const Vector2D<T> * other);
Vector2D<T> Vector2D_int_operator*(struct Vector2D_int * this, int scalar);
bool Vector2D_int_operator==(struct Vector2D_int * this, const Vector2D<T> * other);
bool Vector2D_int_operator!=(struct Vector2D_int * this, const Vector2D<T> * other);
int Vector2D_int_operator[](struct Vector2D_int * this, int index);
struct Vector2D_double {
	double x;
	double y;
};
double Vector2D_double_getX(struct Vector2D_double * this);
double Vector2D_double_getY(struct Vector2D_double * this);
Vector2D<T> Vector2D_double_operator+(struct Vector2D_double * this, const Vector2D<T> * other);
Vector2D<T> Vector2D_double_operator-(struct Vector2D_double * this, const Vector2D<T> * other);
Vector2D<T> Vector2D_double_operator*(struct Vector2D_double * this, double scalar);
bool Vector2D_double_operator==(struct Vector2D_double * this, const Vector2D<T> * other);
bool Vector2D_double_operator!=(struct Vector2D_double * this, const Vector2D<T> * other);
double Vector2D_double_operator[](struct Vector2D_double * this, int index);
