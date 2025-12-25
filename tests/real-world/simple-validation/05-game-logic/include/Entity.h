#ifndef ENTITY_H
#define ENTITY_H

class Entity {
protected:
    float x, y;
    float width, height;

public:
    Entity(float x, float y, float width, float height);
    virtual ~Entity();

    float getX() const;
    float getY() const;
    float getWidth() const;
    float getHeight() const;

    void setPosition(float newX, float newY);
    virtual void update(float deltaTime) = 0;  // Pure virtual
};

#endif // ENTITY_H
