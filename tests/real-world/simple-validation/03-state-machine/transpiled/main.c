#include "main.h"

const char * stateToString(GameState state) {
	switch (state) 	{
	}

}

int main() {
	struct StateMachine sm = (StateMachine){Menu};
	printf("State Machine Tests:\n");
	printf("  Initial state: %s\n", stateToString(getCurrentState(sm)));
	transition(sm, Playing);
	printf("  After Menu -> Playing: %s\n", stateToString(getCurrentState(sm)));
	transition(sm, Paused);
	printf("  After Playing -> Paused: %s\n", stateToString(getCurrentState(sm)));
	transition(sm, Playing);
	printf("  After Paused -> Playing: %s\n", stateToString(getCurrentState(sm)));
	transition(sm, GameOver);
	printf("  After Playing -> GameOver: %s\n", stateToString(getCurrentState(sm)));
	transition(sm, Playing);
	printf("  After GameOver -> Playing (invalid): %s\n", stateToString(getCurrentState(sm)));
	transition(sm, Menu);
	printf("  After GameOver -> Menu: %s\n", stateToString(getCurrentState(sm)));
	printf("  Total valid transitions: %d\n", getTransitionCount(sm));
	bool passed = 1;
	passed = passed && (StateMachine_getCurrentState(sm) == Menu);
	passed = passed && (StateMachine_getTransitionCount(sm) == 5);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
}

