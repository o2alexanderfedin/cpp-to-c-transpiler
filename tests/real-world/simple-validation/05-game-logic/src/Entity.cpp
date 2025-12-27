#include "Entity.h"

Entity::Entity(float x, float y, float width, float height)
    : x(x), y(y), width(width), height(height) {}

Entity::~Entity() {}

float Entity::getX() const { return x; }
float Entity::getY() const { return y; }
float Entity::getWidth() const { return width; }
float Entity::getHeight() const { return height; }

void Entity::setPosition(float newX, float newY) {
    x = newX;
    y = newY;
}
