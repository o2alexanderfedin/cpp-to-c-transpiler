// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Enemy.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/Entity.h"

static void Entity__ctor_copy(struct Entity * this, const struct Entity * other);
struct Enemy {
	const struct Entity_vtable * vptr;
	float x;
	float y;
	float width;
	float height;
	int damage;
	float speed;
};
static void Enemy__ctor_copy(struct Enemy * this, const struct Enemy * other);
void Enemy__dtor(struct Enemy * this);
void Enemy__ctor_2(struct Enemy * this, float x, float y);
int Enemy_getDamage(struct Enemy * this);
