#ifndef COLLISION_DETECTOR_H
#define COLLISION_DETECTOR_H

#include "Entity.h"

class CollisionDetector {
public:
    static bool checkCollision(const Entity& a, const Entity& b);
    static bool pointInside(float px, float py, const Entity& entity);
};

#endif // COLLISION_DETECTOR_H
