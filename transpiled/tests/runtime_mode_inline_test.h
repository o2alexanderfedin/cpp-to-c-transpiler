// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/runtime_mode_inline_test.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

typedef enum {
    Exceptions = 0,
    RTTI = 1,
    Memory = 2,
    VInherit = 3
} RuntimeFeature;
struct RuntimeModeInline {
	int usedFeatures_;
};
static void RuntimeModeInline__ctor_copy(struct RuntimeModeInline * this, const struct RuntimeModeInline * other);
int TEST(int, int mode);
int TEST_int_int(int, int runtime);
int TEST_int_int_1(int, int runtime);
int TEST_int_int_2(int, int runtime);
int TEST_int_int_3(int, int inheritance);
void RuntimeModeInline_markFeatureUsed(struct RuntimeModeInline * this, RuntimeFeature feature);
int TEST_int_int_4(int, int compilation);
int TEST_int_int_5(int, int features);
int TEST_int_int_6(int, int guards);
int TEST_int_int_7(int, int transpilation);
