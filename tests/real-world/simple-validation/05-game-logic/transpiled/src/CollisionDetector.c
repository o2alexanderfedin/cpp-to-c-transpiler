#include "CollisionDetector.h"

bool CollisionDetector__checkCollision__constclassEntityref_constclassEntityref(const struct Entity * a, const struct Entity * b) {
	float aLeft = Entity_getX(&a);
	float aRight = Entity_getX(&a) + Entity_getWidth(&a);
	float aTop = Entity_getY(&a);
	float aBottom = Entity_getY(&a) + Entity_getHeight(&a);
	float bLeft = Entity_getX(&b);
	float bRight = Entity_getX(&b) + Entity_getWidth(&b);
	float bTop = Entity_getY(&b);
	float bBottom = Entity_getY(&b) + Entity_getHeight(&b);
	return !(aRight < bLeft || aLeft > bRight || aBottom < bTop || aTop > bBottom);
;
}

bool CollisionDetector__pointInside__float_float_constclassEntityref(float px, float py, const struct Entity * entity) {
	return px >= Entity_getX(&entity) && px <= Entity_getX(&entity) + Entity_getWidth(&entity) && py >= Entity_getY(&entity) && py <= Entity_getY(&entity) + Entity_getHeight(&entity);
;
}

