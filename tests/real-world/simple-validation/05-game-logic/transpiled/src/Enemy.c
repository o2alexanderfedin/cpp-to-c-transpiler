#include "Enemy.h"

int Enemy__getDamage__void(struct Enemy * this) {
	return this->damage;
;
}

void Enemy__update__float(struct Enemy * this, float deltaTime) {
	this->x = this->x - this->speed * deltaTime;
}

