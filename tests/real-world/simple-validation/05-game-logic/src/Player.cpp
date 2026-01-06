#include "Player.h"

Player::Player(float x, float y)
    : Entity(x, y, 32.0f, 32.0f), health(100), score(0) {}

Player::~Player() {}

int Player::getHealth() const { return health; }
int Player::getScore() const { return score; }

void Player::takeDamage(int damage) {
    health -= damage;
    if (health < 0) {
        health = 0;
    }
}

void Player::addScore(int points) {
    score += points;
}

void Player::update(float deltaTime) {
    // Player update logic (placeholder)
}
