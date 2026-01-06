#include "CollisionDetector.h"

bool CollisionDetector::checkCollision(const Entity& a, const Entity& b) {
    // AABB (Axis-Aligned Bounding Box) collision detection
    float aLeft = a.getX();
    float aRight = a.getX() + a.getWidth();
    float aTop = a.getY();
    float aBottom = a.getY() + a.getHeight();

    float bLeft = b.getX();
    float bRight = b.getX() + b.getWidth();
    float bTop = b.getY();
    float bBottom = b.getY() + b.getHeight();

    return !(aRight < bLeft || aLeft > bRight ||
             aBottom < bTop || aTop > bBottom);
}

bool CollisionDetector::pointInside(float px, float py, const Entity& entity) {
    return px >= entity.getX() &&
           px <= entity.getX() + entity.getWidth() &&
           py >= entity.getY() &&
           py <= entity.getY() + entity.getHeight();
}
