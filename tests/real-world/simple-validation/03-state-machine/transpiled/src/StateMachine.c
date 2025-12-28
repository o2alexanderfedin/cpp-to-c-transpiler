// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/src/StateMachine.cpp
// Implementation file

#include "StateMachine.h"

static void StateMachine__ctor_copy(struct StateMachine * this, const struct StateMachine * other) {
	this->currentState = other->currentState;
	this->transitionCount = other->transitionCount;
}

void StateMachine__ctor_1(struct StateMachine * this, GameState initialState) {
	this->currentState = initialState;
	this->transitionCount = 0;
}

bool StateMachine_isValidTransition_GameState_GameState(struct StateMachine * this, GameState from, GameState to);
GameState StateMachine_getCurrentState(struct StateMachine * this) {
	return this->currentState;
;
}

int StateMachine_getTransitionCount(struct StateMachine * this) {
	return this->transitionCount;
;
}

bool StateMachine_isValidTransition_GameState_GameState(struct StateMachine * this, GameState from, GameState to) {
	switch (from) 	{
		case GameState__Menu:
			return to == GameState__Playing;
;
		case GameState__Playing:
			return to == GameState__Paused || to == GameState__GameOver;
;
		case GameState__Paused:
			return to == GameState__Playing || to == GameState__Menu || to == GameState__GameOver;
;
		case GameState__GameOver:
			return to == GameState__Menu;
;
		default:
			return false;
;
	}

}

