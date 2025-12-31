// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/Player.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/Entity.h"

void Player__ctor_2(struct Player * this, float x, float y);
extern int Player_getHealth(struct Player * this);
extern int Player_getScore(struct Player * this);
extern void Player_takeDamage_int(struct Player * this, int damage);
extern void Player_addScore_int(struct Player * this, int points);
