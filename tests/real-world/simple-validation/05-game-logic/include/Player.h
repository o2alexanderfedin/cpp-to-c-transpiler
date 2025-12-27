#ifndef PLAYER_H
#define PLAYER_H

#include "Entity.h"

class Player : public Entity {
private:
    int health;
    int score;

public:
    Player(float x, float y);
    ~Player() override;

    int getHealth() const;
    int getScore() const;

    void takeDamage(int damage);
    void addScore(int points);
    void update(float deltaTime) override;
};

#endif // PLAYER_H
