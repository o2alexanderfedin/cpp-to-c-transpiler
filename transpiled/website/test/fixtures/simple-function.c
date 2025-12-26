// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/simple-function.cpp
// Implementation file

#include "simple-function.h"

int add(int a, int b) {
	return a + b;
;
}

int multiply(int x, int y) {
	return x * y;
;
}

double divide(double numerator, double denominator) {
	if (denominator == 0.) 	{
		return 0.;
;
	}

	return numerator / denominator;
;
}

