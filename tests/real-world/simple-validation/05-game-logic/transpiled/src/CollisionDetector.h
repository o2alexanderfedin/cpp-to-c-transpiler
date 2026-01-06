#pragma once

struct CollisionDetector {
};
bool CollisionDetector__checkCollision__constclassEntityref_constclassEntityref(const struct Entity * a, const struct Entity * b);
bool CollisionDetector__pointInside__float_float_constclassEntityref(float px, float py, const struct Entity * entity);
