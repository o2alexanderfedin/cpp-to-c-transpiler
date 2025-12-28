// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/main.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct StateMachine {
	GameState currentState;
	int transitionCount;
};
static void StateMachine__ctor_copy(struct StateMachine * this, const struct StateMachine * other);
const char * stateToString(GameState state);
GameState StateMachine_getCurrentState(struct StateMachine * this);
void StateMachine_transition(struct StateMachine * this, GameState newState);
int StateMachine_getTransitionCount(struct StateMachine * this);
int main();
