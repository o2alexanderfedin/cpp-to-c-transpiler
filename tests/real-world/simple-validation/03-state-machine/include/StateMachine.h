#ifndef STATEMACHINE_H
#define STATEMACHINE_H

#include "GameState.h"

class StateMachine {
private:
    GameState currentState;
    int transitionCount;

public:
    StateMachine(GameState initialState);
    void transition(GameState newState);
    GameState getCurrentState() const;
    int getTransitionCount() const;
    bool isValidTransition(GameState from, GameState to) const;
};

#endif // STATEMACHINE_H
