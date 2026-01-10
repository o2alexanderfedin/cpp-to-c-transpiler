#pragma once

int Player__getHealth__void(struct Player * this);
int Player__getScore__void(struct Player * this);
void Player__takeDamage__int(struct Player * this, int damage);
void Player__addScore__int(struct Player * this, int points);
void Player__update__float(struct Player * this, float deltaTime);
