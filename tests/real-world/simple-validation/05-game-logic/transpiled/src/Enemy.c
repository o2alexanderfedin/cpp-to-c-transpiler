// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Enemy.cpp
// Implementation file

#include "Enemy.h"

static void Entity__ctor_copy(struct Entity * this, const struct Entity * other) {
	this->x = other->x;
	this->y = other->y;
	this->width = other->width;
	this->height = other->height;
}

static void Enemy__ctor_copy(struct Enemy * this, const struct Enemy * other) {
	this->damage = other->damage;
	this->speed = other->speed;
}

void Enemy__dtor(struct Enemy * this) {
	Entity__dtor(this);
}

void Enemy__ctor_2(struct Enemy * this, float x, float y) {
	this = &__vtable_Enemy;
	Entity__ctor_4(this, x, y, 24.F, 24.F);
	this->damage = 10;
	this->speed = 50.F;
}

int Enemy_getDamage(struct Enemy * this) {
	return this->damage;
;
}

