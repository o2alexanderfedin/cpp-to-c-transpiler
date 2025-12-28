// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/src/StateMachine.cpp
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
void StateMachine__ctor(struct StateMachine * this, GameState initialState);
bool StateMachine_isValidTransition(struct StateMachine * this, GameState from, GameState to);
GameState StateMachine_getCurrentState(struct StateMachine * this);
int StateMachine_getTransitionCount(struct StateMachine * this);
bool StateMachine_isValidTransition_GameState_GameState(struct StateMachine * this, GameState from, GameState to);
