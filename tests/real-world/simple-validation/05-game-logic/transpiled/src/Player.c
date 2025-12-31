// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Player.cpp
// Implementation file

#include "Player.h"

void Player__ctor_2(struct Player * this, float x, float y) {
	this = &__vtable_Player;
	this->health = 100;
	this->score = 0;
}

extern int Player_getHealth(struct Player * this) {
	return this->health;
;
}

extern int Player_getScore(struct Player * this) {
	return this->score;
;
}

extern void Player_takeDamage_int(struct Player * this, int damage) {
	this->health -= damage;
	if (this->health < 0) 	{
		this->health = 0;
	}

}

extern void Player_addScore_int(struct Player * this, int points) {
	this->score += points;
}

