// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Player.cpp
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
int Player_getHealth(struct Player * this);
int Player_getScore(struct Player * this);
void Player_takeDamage(struct Player * this, int damage);
void Player_addScore(struct Player * this, int points);
void Player__ctor(struct Player * this, float x, float y);
