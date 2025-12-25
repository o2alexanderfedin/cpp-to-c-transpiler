// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/main.cpp
// Implementation file

#include "main.h"

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

static void Enemy__ctor_copy(struct Enemy * this, const struct Enemy * other) {
	this->damage = other->damage;
	this->speed = other->speed;
}

void Enemy__dtor(struct Enemy * this) {
	Entity__dtor(this);
}

static void CollisionDetector__ctor_default(struct CollisionDetector * this) {
}

static void CollisionDetector__ctor_copy(struct CollisionDetector * this, const struct CollisionDetector * other) {
}

void Entity_setPosition(struct Entity * this, float newX, float newY);
int Enemy_getDamage(struct Enemy * this);
void Player_takeDamage(struct Player * this, int damage);
void Player_addScore(struct Player * this, int points);
int Player_getHealth(struct Player * this);
int Player_getScore(struct Player * this);
int main() {
	struct Player player;

	struct Enemy enemy;

	bool colliding1 = CollisionDetector::checkCollision(player, enemy);

	Entity_setPosition(&enemy, 110.F, 100.F);
	bool colliding2 = CollisionDetector::checkCollision(player, enemy);

	Player_takeDamage(&player, Enemy_getDamage(&enemy));
	Player_addScore(&player, 100);
	bool inside = CollisionDetector::pointInside(115.F, 115.F, player);

	bool passed = true;

	passed = passed && (player.getHealth() == 90);
	passed = passed && (player.getScore() == 100);
	passed = passed && (colliding1 == false);
	passed = passed && (colliding2 == true);
	passed = passed && (inside == true);
	return passed ? 0 : 1;
;
	Enemy__dtor(&enemy);
	Player__dtor(&player);
}

