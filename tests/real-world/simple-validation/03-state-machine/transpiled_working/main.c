// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/./main.cpp
// Implementation file

#include "main.h"

static void StateMachine__ctor_copy(struct StateMachine * this, const struct StateMachine * other) {
	this->currentState = other->currentState;
	this->transitionCount = other->transitionCount;
}

const char * stateToString(int state) {
	switch (state) 	{
		case GameState__Menu:
			return "Menu";
;
		case GameState__Playing:
			return "Playing";
;
		case GameState__Paused:
			return "Paused";
;
		case GameState__GameOver:
			return "GameOver";
;
		default:
			return "Unknown";
;
	}

}

int main() {
	struct StateMachine sm;
	StateMachine__ctor_1(&sm, GameState__Menu);
	StateMachine_transition_GameState(&sm, GameState__Playing);
	StateMachine_transition_GameState(&sm, GameState__Paused);
	StateMachine_transition_GameState(&sm, GameState__Playing);
	StateMachine_transition_GameState(&sm, GameState__GameOver);
	StateMachine_transition_GameState(&sm, GameState__Playing);
	StateMachine_transition_GameState(&sm, GameState__Menu);
	bool passed = true;
	passed = passed && (StateMachine_getCurrentState(&sm) == GameState__Menu);
	passed = passed && (StateMachine_getTransitionCount(&sm) == 5);
	return passed ? 0 : 1;
;
}

