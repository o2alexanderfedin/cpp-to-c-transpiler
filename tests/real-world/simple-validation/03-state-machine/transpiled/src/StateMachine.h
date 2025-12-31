// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/src/StateMachine.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>


void StateMachine__ctor_1(struct StateMachine * this, int initialState);
extern void StateMachine_transition_GameState(struct StateMachine * this, int newState);
extern int StateMachine_getCurrentState(struct StateMachine * this);
extern int StateMachine_getTransitionCount(struct StateMachine * this);
extern bool StateMachine_isValidTransition_GameState_GameState(struct StateMachine * this, int from, int to);
