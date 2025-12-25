#ifndef ENEMY_H
#define ENEMY_H

#include "Entity.h"

class Enemy : public Entity {
private:
    int damage;
    float speed;

public:
    Enemy(float x, float y);
    ~Enemy() override;

    int getDamage() const;
    void update(float deltaTime) override;
};

#endif // ENEMY_H
