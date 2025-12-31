// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/class-inheritance.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct Shape {
	const struct Shape_vtable * vptr;
	int width;
	int height;
};
static void Shape__ctor_copy(struct Shape * this, const struct Shape * other);
void Shape__ctor_2(struct Shape * this, int w, int h);
int Shape_getWidth(struct Shape * this);
int Shape_getHeight(struct Shape * this);
struct Rectangle {
	const struct Shape_vtable * vptr;
	int width;
	int height;
};
static void Rectangle__ctor_copy(struct Rectangle * this, const struct Rectangle * other);
void Rectangle__ctor_2(struct Rectangle * this, int w, int h);
struct Triangle {
	const struct Shape_vtable * vptr;
	int width;
	int height;
};
static void Triangle__ctor_copy(struct Triangle * this, const struct Triangle * other);
void Triangle__ctor_2(struct Triangle * this, int w, int h);
