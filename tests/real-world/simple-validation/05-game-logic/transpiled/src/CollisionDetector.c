// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/CollisionDetector.cpp
// Implementation file

#include "CollisionDetector.h"

static void Entity__ctor_copy(struct Entity * this, const struct Entity * other) {
	this->x = other->x;
	this->y = other->y;
	this->width = other->width;
	this->height = other->height;
}

void Entity__dtor(struct Entity * this) {
}

static void CollisionDetector__ctor_default(struct CollisionDetector * this) {
}

static void CollisionDetector__ctor_copy(struct CollisionDetector * this, const struct CollisionDetector * other) {
}

float Entity_getX(struct Entity * this);
float Entity_getWidth(struct Entity * this);
float Entity_getY(struct Entity * this);
float Entity_getHeight(struct Entity * this);
bool CollisionDetector_checkCollision(struct CollisionDetector * this, const struct Entity * a, const struct Entity * b) {
	float aLeft = Entity_getX(&a);

	float aRight = Entity_getX(&a) + Entity_getWidth(&a);

	float aTop = Entity_getY(&a);

	float aBottom = Entity_getY(&a) + Entity_getHeight(&a);

	float bLeft = Entity_getX(&b);

	float bRight = Entity_getX(&b) + Entity_getWidth(&b);

	float bTop = Entity_getY(&b);

	float bBottom = Entity_getY(&b) + Entity_getHeight(&b);

	return !(aRight < bLeft || aLeft > bRight || aBottom < bTop || aTop > bBottom);
;
}

bool CollisionDetector_pointInside(struct CollisionDetector * this, float px, float py, const struct Entity * entity) {
	return px >= Entity_getX(&entity) && px <= Entity_getX(&entity) + Entity_getWidth(&entity) && py >= Entity_getY(&entity) && py <= Entity_getY(&entity) + Entity_getHeight(&entity);
;
}

