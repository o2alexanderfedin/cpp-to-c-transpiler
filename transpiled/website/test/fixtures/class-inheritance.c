// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/class-inheritance.cpp
// Implementation file

#include "class-inheritance.h"

static void Shape__ctor_copy(struct Shape * this, const struct Shape * other) {
	this->vptr = other->vptr;
	this->width = other->width;
	this->height = other->height;
}

void Shape__ctor_2(struct Shape * this, int w, int h) {
	this = &__vtable_Shape;
	this->width = w;
	this->height = h;
}

int Shape_getWidth(struct Shape * this) {
	return this->width;
;
}

int Shape_getHeight(struct Shape * this) {
	return this->height;
;
}

static void Rectangle__ctor_copy(struct Rectangle * this, const struct Rectangle * other) {
	this->vptr = other->vptr;
	this->width = other->width;
	this->height = other->height;
}

void Rectangle__ctor_2(struct Rectangle * this, int w, int h) {
	this = &__vtable_Rectangle;
	Shape__ctor_2(this, w, h);
}

static void Triangle__ctor_copy(struct Triangle * this, const struct Triangle * other) {
	this->vptr = other->vptr;
	this->width = other->width;
	this->height = other->height;
}

void Triangle__ctor_2(struct Triangle * this, int w, int h) {
	this = &__vtable_Triangle;
	Shape__ctor_2(this, w, h);
}

