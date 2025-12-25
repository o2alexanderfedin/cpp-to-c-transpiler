// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Enemy.cpp
// Implementation file

#include "Enemy.h"

static void Entity__ctor_copy(struct Entity * this, const struct Entity * other) {
	this->x = other->x;
	this->y = other->y;
	this->width = other->width;
	this->height = other->height;
}

void Entity__dtor(struct Entity * this) {
}

static void Enemy__ctor_copy(struct Enemy * this, const struct Enemy * other) {
	this->damage = other->damage;
	this->speed = other->speed;
}

void Enemy__dtor(struct Enemy * this) {
	Entity__dtor(this);
}

int Enemy_getDamage(struct Enemy * this) {
	return this->damage;

}

void Enemy__ctor(struct Enemy * this, float x, float y) {
	this = &__vtable_Enemy;
	this->damage = 10;
	this->speed = 50.F;
}

