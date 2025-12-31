// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/main.cpp
// Implementation file

#include "main.h"

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
	printf("State Machine Tests:\n");
	printf("  Initial state: %s\n", stateToString(StateMachine_getCurrentState(&sm)));
	StateMachine_transition_GameState(&sm, GameState__Playing);
	printf("  After Menu -> Playing: %s\n", stateToString(StateMachine_getCurrentState(&sm)));
	StateMachine_transition_GameState(&sm, GameState__Paused);
	printf("  After Playing -> Paused: %s\n", stateToString(StateMachine_getCurrentState(&sm)));
	StateMachine_transition_GameState(&sm, GameState__Playing);
	printf("  After Paused -> Playing: %s\n", stateToString(StateMachine_getCurrentState(&sm)));
	StateMachine_transition_GameState(&sm, GameState__GameOver);
	printf("  After Playing -> GameOver: %s\n", stateToString(StateMachine_getCurrentState(&sm)));
	StateMachine_transition_GameState(&sm, GameState__Playing);
	printf("  After GameOver -> Playing (invalid): %s\n", stateToString(StateMachine_getCurrentState(&sm)));
	StateMachine_transition_GameState(&sm, GameState__Menu);
	printf("  After GameOver -> Menu: %s\n", stateToString(StateMachine_getCurrentState(&sm)));
	printf("  Total valid transitions: %d\n", StateMachine_getTransitionCount(&sm));
	bool passed = true;
	passed = passed && (StateMachine_getCurrentState(&sm) == GameState__Menu);
	passed = passed && (StateMachine_getTransitionCount(&sm) == 5);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
}

