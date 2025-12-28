// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Entity.cpp
// Implementation file

#include "Entity.h"

static void Entity__ctor_copy(struct Entity * this, const struct Entity * other) {
	this->x = other->x;
	this->y = other->y;
	this->width = other->width;
	this->height = other->height;
}

void Entity__dtor(struct Entity * this) {
}

void Entity__ctor(struct Entity * this, float x, float y, float width, float height) {
	this = &__vtable_Entity;
	this->x = x;
	this->y = y;
	this->width = width;
	this->height = height;
}

float Entity_getX(struct Entity * this) {
	return this->x;
;
}

float Entity_getY(struct Entity * this) {
	return this->y;
;
}

float Entity_getWidth(struct Entity * this) {
	return this->width;
;
}

float Entity_getHeight(struct Entity * this) {
	return this->height;
;
}

void Entity_setPosition(struct Entity * this, float newX, float newY) {
	this->x = newX;
	this->y = newY;
}

