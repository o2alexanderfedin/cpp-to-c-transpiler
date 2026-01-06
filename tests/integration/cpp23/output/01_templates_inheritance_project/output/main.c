// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/01_templates_inheritance_project/main.cpp
// Implementation file

#include "main.h"

int main() {
	struct Box_int intBox;
	struct Box_double doubleBox;
	return 0;
;
}

int Box_int_getValue(struct Box_int * this) {
	return this->value * this->multiplier;
;
}

int Box_int_getMultiplier(struct Box_int * this) {
	return this->multiplier;
;
}

double Box_double_getValue(struct Box_double * this) {
	return this->value * this->multiplier;
;
}

double Box_double_getMultiplier(struct Box_double * this) {
	return this->multiplier;
;
}

