#include "Entity.h"

float Entity__getX__void(struct Entity * this) {
	return this->x;
;
}

float Entity__getY__void(struct Entity * this) {
	return this->y;
;
}

float Entity__getWidth__void(struct Entity * this) {
	return this->width;
;
}

float Entity__getHeight__void(struct Entity * this) {
	return this->height;
;
}

void Entity__setPosition__float_float(struct Entity * this, float newX, float newY) {
	this->x = newX;
	this->y = newY;
}

