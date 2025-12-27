#include "StateMachine.h"

StateMachine::StateMachine(GameState initialState)
    : currentState(initialState), transitionCount(0) {}

void StateMachine::transition(GameState newState) {
    if (isValidTransition(currentState, newState)) {
        currentState = newState;
        transitionCount++;
    }
}

GameState StateMachine::getCurrentState() const {
    return currentState;
}

int StateMachine::getTransitionCount() const {
    return transitionCount;
}

bool StateMachine::isValidTransition(GameState from, GameState to) const {
    // Define valid state transitions
    switch (from) {
        case GameState::Menu:
            return to == GameState::Playing;

        case GameState::Playing:
            return to == GameState::Paused || to == GameState::GameOver;

        case GameState::Paused:
            return to == GameState::Playing || to == GameState::Menu || to == GameState::GameOver;

        case GameState::GameOver:
            return to == GameState::Menu;

        default:
            return false;
    }
}
