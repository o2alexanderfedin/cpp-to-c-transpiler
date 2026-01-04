#include "main.h"

int main() {
	int v1 = 0;
	int v2 = 0;
	int sum = 0;
	float dot = 0(0);
	int cross = 0;
	0;
	0("  v1 = (%.1f, %.1f, %.1f)\n", 0, 0, 0);
	0("  v2 = (%.1f, %.1f, %.1f)\n", 0, 0, 0);
	0("  v1 + v2 = (%.1f, %.1f, %.1f)\n", 0, 0, 0);
	0;
	0("  v1 x v2 = (%.1f, %.1f, %.1f)\n", 0, 0, 0);
	int m1 = 0;
	int m2 = 0;
	int mProd = 0;
	int transformed = 0;
	0;
	0("  Identity * 2I = 2I (first element: %.1f)\n", 0(0, 0));
	0("  2I * v1 = (%.1f, %.1f, %.1f)\n", 0, 0, 0);
	bool passed = 1;
	passed = passed && (0(0 - 5.F) < 0.00100000005F);
	passed = passed && (0(0 - 7.F) < 0.00100000005F);
	passed = passed && (0(0 - 9.F) < 0.00100000005F);
	passed = passed && (0 < 0.00100000005F);
	passed = passed && (0(0 - (-3.F)) < 0.00100000005F);
	passed = passed && (0(0 - 6.F) < 0.00100000005F);
	passed = passed && (0(0 - (-3.F)) < 0.00100000005F);
	passed = passed && (0(0(0, 0) - 2.F) < 0.00100000005F);
	passed = passed && (0(0 - 2.F) < 0.00100000005F);
	0;
	return passed ? 0 : 1;
;
}

