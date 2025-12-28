// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Entity.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct Entity {
	const struct Entity_vtable * vptr;
	float x;
	float y;
	float width;
	float height;
};
static void Entity__ctor_copy(struct Entity * this, const struct Entity * other);
void Entity__dtor(struct Entity * this);
void Entity__ctor(struct Entity * this, float x, float y, float width, float height);
float Entity_getX(struct Entity * this);
float Entity_getY(struct Entity * this);
float Entity_getWidth(struct Entity * this);
float Entity_getHeight(struct Entity * this);
void Entity_setPosition(struct Entity * this, float newX, float newY);
