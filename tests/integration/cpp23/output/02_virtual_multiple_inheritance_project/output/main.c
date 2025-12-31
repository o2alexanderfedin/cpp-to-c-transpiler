// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/02_virtual_multiple_inheritance_project/main.cpp
// Implementation file

#include "main.h"

static void Base__ctor_copy(struct Base * this, const struct Base * other) {
	this->baseValue = other->baseValue;
}

void Base__ctor(struct Base * this, int v) {
	this = &__vtable_Base;
	this->baseValue = v;
}

void Base__dtor(struct Base * this) {
}

int Base_getBaseValue(struct Base * this) {
	return this->baseValue;
;
}

static void Left__ctor_copy(struct Left * this, const struct Left * other) {
	this->leftValue = other->leftValue;
}

void Left__ctor(struct Left * this, int b, int l) {
	this = &__vtable_Left;
	Base__ctor(this, b);
	this->leftValue = l;
}

int Left_getLeftValue(struct Left * this) {
	return this->leftValue;
;
}

static void Right__ctor_copy(struct Right * this, const struct Right * other) {
	this->rightValue = other->rightValue;
}

void Right__ctor(struct Right * this, int b, int r) {
	this = &__vtable_Right;
	Base__ctor(this, b);
	this->rightValue = r;
}

int Right_getRightValue(struct Right * this) {
	return this->rightValue;
;
}

static void Diamond__ctor_copy(struct Diamond * this, const struct Diamond * other) {
	this->diamondValue = other->diamondValue;
}

void Diamond__ctor(struct Diamond * this, int b1, int l, int b2, int r, int d) {
	this = &__vtable_Diamond;
	Left__ctor(this, b1, l);
	Right__ctor(this, b2, r);
	this->diamondValue = d;
}

int Diamond_getDiamondValue(struct Diamond * this) {
	return this->diamondValue;
;
}

int main() {
	struct Diamond d;
	Diamond__ctor(&d, 10, 5, 3, 4, 7);
	return 0;
;
}

