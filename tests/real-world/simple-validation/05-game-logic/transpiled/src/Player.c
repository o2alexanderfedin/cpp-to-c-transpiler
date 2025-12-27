// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Player.cpp
// Implementation file

#include "Player.h"

static void Entity__ctor_copy(struct Entity * this, const struct Entity * other) {
	this->x = other->x;
	this->y = other->y;
	this->width = other->width;
	this->height = other->height;
}

void Entity__dtor(struct Entity * this) {
}

static void Player__ctor_copy(struct Player * this, const struct Player * other) {
	this->health = other->health;
	this->score = other->score;
}

void Player__dtor(struct Player * this) {
	Entity__dtor(this);
}

int Player_getHealth(struct Player * this) {
	return this->health;
;
}

int Player_getScore(struct Player * this) {
	return this->score;
;
}

void Player_takeDamage(struct Player * this, int damage) {
	this->health -= damage;
	if (this->health < 0) 	{
		this->health = 0;
	}

}

void Player_addScore(struct Player * this, int points) {
	this->score += points;
}

void Player__ctor(struct Player * this, float x, float y) {
	this = &__vtable_Player;
	this->health = 100;
	this->score = 0;
}

