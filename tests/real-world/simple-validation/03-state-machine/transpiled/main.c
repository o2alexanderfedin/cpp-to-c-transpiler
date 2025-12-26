// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/main.cpp
// Implementation file

#include "main.h"

static void StateMachine__ctor_copy(struct StateMachine * this, const struct StateMachine * other) {
	this->currentState = other->currentState;
	this->transitionCount = other->transitionCount;
}

const char * stateToString(GameState state) {
	switch (state) 	{
		case GameState::Menu:
			return "Menu";
;
		case GameState::Playing:
			return "Playing";
;
		case GameState::Paused:
			return "Paused";
;
		case GameState::GameOver:
			return "GameOver";
;
		default:
			return "Unknown";
;
	}

}

void StateMachine_transition(struct StateMachine * this, GameState newState);
GameState StateMachine_getCurrentState(struct StateMachine * this);
int StateMachine_getTransitionCount(struct StateMachine * this);
int main() {
	struct StateMachine sm;

	StateMachine_transition(&sm, 1);
	StateMachine_transition(&sm, 2);
	StateMachine_transition(&sm, 1);
	StateMachine_transition(&sm, 3);
	StateMachine_transition(&sm, 1);
	StateMachine_transition(&sm, 0);
	bool passed = true;

	passed = passed && (sm.getCurrentState() == GameState::Menu);
	passed = passed && (sm.getTransitionCount() == 5);
	return passed ? 0 : 1;
;
}

