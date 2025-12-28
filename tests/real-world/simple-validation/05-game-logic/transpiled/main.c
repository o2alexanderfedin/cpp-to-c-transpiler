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

float Entity_getX(struct Entity * this);
float Entity_getY(struct Entity * this);
int Player_getHealth(struct Player * this);
int Player_getScore(struct Player * this);
int Enemy_getDamage(struct Enemy * this);
void Entity_setPosition(struct Entity * this, float newX, float newY);
void Player_takeDamage(struct Player * this, int damage);
void Player_addScore(struct Player * this, int points);
int main() {
	printf("Game Logic Tests:\n");
	struct Player player;
	struct Enemy enemy;
	printf("  Player: pos=(%.1f, %.1f), health=%d, score=%d\n", Entity_getX(&player), Entity_getY(&player), Player_getHealth(&player), Player_getScore(&player));
	printf("  Enemy: pos=(%.1f, %.1f), damage=%d\n", Entity_getX(&enemy), Entity_getY(&enemy), Enemy_getDamage(&enemy));
	bool colliding1 = CollisionDetector::checkCollision(player, enemy);
	printf("  Initial collision: %s\n", colliding1 ? "true" : "false");
	Entity_setPosition(&enemy, 110.F, 100.F);
	bool colliding2 = CollisionDetector::checkCollision(player, enemy);
	printf("  After enemy moves to (110, 100): collision = %s\n", colliding2 ? "true" : "false");
	printf("  Player takes %d damage\n", Enemy_getDamage(&enemy));
	Player_takeDamage(&player, Enemy_getDamage(&enemy));
	printf("  Player health after damage: %d\n", Player_getHealth(&player));
	Player_addScore(&player, 100);
	printf("  Player score after +100: %d\n", Player_getScore(&player));
	bool inside = CollisionDetector::pointInside(115.F, 115.F, player);
	printf("  Point (115, 115) inside player: %s\n", inside ? "true" : "false");
	bool passed = true;
	passed = passed && (Player_getHealth(&player) == 90);
	passed = passed && (Player_getScore(&player) == 100);
	passed = passed && (colliding1 == false);
	passed = passed && (colliding2 == true);
	passed = passed && (inside == true);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
	Enemy__dtor(&enemy);
	Player__dtor(&player);
}

