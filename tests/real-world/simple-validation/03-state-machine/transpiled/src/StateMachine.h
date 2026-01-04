#pragma once

struct StateMachine {
	GameState currentState;
	int transitionCount;
};
void StateMachine__transition__GameState(struct StateMachine * this, GameState newState);
GameState StateMachine__getCurrentState__void(struct StateMachine * this);
int StateMachine__getTransitionCount__void(struct StateMachine * this);
bool StateMachine__isValidTransition__GameState_GameState(struct StateMachine * this, GameState from, GameState to);
