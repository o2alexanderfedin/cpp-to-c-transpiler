#include "Player.h"

int Player__getHealth__void(struct Player * this) {
	return this->health;
;
}

int Player__getScore__void(struct Player * this) {
	return this->score;
;
}

void Player__takeDamage__int(struct Player * this, int damage) {
	this->health = this->health - damage;
	if (this->health < 0) 	{
		this->health = 0;
	}

}

void Player__addScore__int(struct Player * this, int points) {
	this->score = this->score + points;
}

void Player__update__float(struct Player * this, float deltaTime) {
}

