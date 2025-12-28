// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/main.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/CollisionDetector.h"
#include "src/Enemy.h"
#include "src/Entity.h"
#include "src/Player.h"

static void Entity__ctor_copy(struct Entity * this, const struct Entity * other);
static void Player__ctor_copy(struct Player * this, const struct Player * other);
static void Enemy__ctor_copy(struct Enemy * this, const struct Enemy * other);
static void CollisionDetector__ctor_default(struct CollisionDetector * this);
static void CollisionDetector__ctor_copy(struct CollisionDetector * this, const struct CollisionDetector * other);
int main();
