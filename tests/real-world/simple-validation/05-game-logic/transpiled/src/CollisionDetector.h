// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/CollisionDetector.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct Entity {
        const struct Entity_vtable *vptr;
        float x;
        float y;
        float width;
        float height;
};
static void Entity__ctor_copy(struct Entity * this, const struct Entity * other);
void Entity__dtor(struct Entity * this);
struct CollisionDetector {
};
static void CollisionDetector__ctor_default(struct CollisionDetector * this);
static void CollisionDetector__ctor_copy(struct CollisionDetector * this, const struct CollisionDetector * other);
float Entity_getX(struct Entity * this);
float Entity_getWidth(struct Entity * this);
float Entity_getY(struct Entity * this);
float Entity_getHeight(struct Entity * this);
bool CollisionDetector_checkCollision(struct CollisionDetector * this, const struct Entity * a, const struct Entity * b);
bool CollisionDetector_pointInside(struct CollisionDetector * this, float px, float py, const struct Entity * entity);
