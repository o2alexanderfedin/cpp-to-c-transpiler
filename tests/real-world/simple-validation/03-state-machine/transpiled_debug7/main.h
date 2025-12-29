// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/main.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/StateMachine.h"

static void StateMachine__ctor_copy(struct StateMachine * this, const struct StateMachine * other);
const char * stateToString(int state);
int main();
