// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/src/StateMachine.cpp
// Implementation file

#include "StateMachine.h"

static void StateMachine__ctor_copy(struct StateMachine * this, const struct StateMachine * other) {
	this->currentState = other->currentState;
	this->transitionCount = other->transitionCount;
}

bool StateMachine_isValidTransition(struct StateMachine * this, GameState from, GameState to);
GameState StateMachine_getCurrentState(struct StateMachine * this) {
	return this->currentState;
;
}

int StateMachine_getTransitionCount(struct StateMachine * this) {
	return this->transitionCount;
;
}

void StateMachine__ctor(struct StateMachine * this, GameState initialState) {
	this->currentState = initialState;
	this->transitionCount = 0;
}

