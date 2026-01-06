// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/./src/Enemy.cpp
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
struct Enemy {
        const struct Entity_vtable *vptr;
        float x;
        float y;
        float width;
        float height;
        int damage;
        float speed;
};
static void Enemy__ctor_copy(struct Enemy * this, const struct Enemy * other);
void Enemy__dtor(struct Enemy * this);
int Enemy_getDamage(struct Enemy * this);
void Enemy__ctor(struct Enemy * this, float x, float y);
