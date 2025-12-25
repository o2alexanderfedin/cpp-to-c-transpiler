#include "Enemy.h"

Enemy::Enemy(float x, float y)
    : Entity(x, y, 24.0f, 24.0f), damage(10), speed(50.0f) {}

Enemy::~Enemy() {}

int Enemy::getDamage() const { return damage; }

void Enemy::update(float deltaTime) {
    // Move enemy left (simple AI)
    x -= speed * deltaTime;
}
