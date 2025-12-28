// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/main.cpp
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
struct Player {
	const struct Entity_vtable * vptr;
	float x;
	float y;
	float width;
	float height;
	int health;
	int score;
};
static void Player__ctor_copy(struct Player * this, const struct Player * other);
void Player__dtor(struct Player * this);
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
struct CollisionDetector {
};
static void CollisionDetector__ctor_default(struct CollisionDetector * this);
static void CollisionDetector__ctor_copy(struct CollisionDetector * this, const struct CollisionDetector * other);
float Entity_getX(struct Entity * this);
float Entity_getY(struct Entity * this);
int Player_getHealth(struct Player * this);
int Player_getScore(struct Player * this);
int Enemy_getDamage(struct Enemy * this);
void Entity_setPosition(struct Entity * this, float newX, float newY);
void Player_takeDamage(struct Player * this, int damage);
void Player_addScore(struct Player * this, int points);
int main();
