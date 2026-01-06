#pragma once

struct StateMachine {
	enum GameState currentState;
	int transitionCount;
};
void StateMachine__transition__enumGameState(struct StateMachine * this, enum GameState newState);
enum GameState StateMachine__getCurrentState__void(struct StateMachine * this);
int StateMachine__getTransitionCount__void(struct StateMachine * this);
bool StateMachine__isValidTransition__enumGameState_enumGameState(struct StateMachine * this, enum GameState from, enum GameState to);
