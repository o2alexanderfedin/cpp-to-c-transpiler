// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/src/CollisionDetector.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/Entity.h"

static void Entity__ctor_copy(struct Entity * this, const struct Entity * other);
struct CollisionDetector {
};
static void CollisionDetector__ctor_default(struct CollisionDetector * this);
static void CollisionDetector__ctor_copy(struct CollisionDetector * this, const struct CollisionDetector * other);
bool CollisionDetector_checkCollision_const_Entity_ref_const_Entity_ref(struct CollisionDetector * this, const struct Entity * a, const struct Entity * b);
bool CollisionDetector_pointInside_float_float_const_Entity_ref(struct CollisionDetector * this, float px, float py, const struct Entity * entity);
