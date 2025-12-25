// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/main.cpp
// Implementation file

#include "main.h"

int main() {
	int player;

	int enemy;

	bool colliding1;

	bool colliding2;

	bool inside;

	bool passed = true;

	passed = passed && (colliding1 == false);
	passed = passed && (colliding2 == true);
	passed = passed && (inside == true);
	return passed ? 0 : 1;

}

