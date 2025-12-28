// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/templates.cpp
// Implementation file

#include "templates.h"

T maximum(T a, T b) {
	return (a > b) ? a : b;
;
}

void swapValues(T * a, T * b) {
	T temp = a;
	a = b;
	b = temp;
}

