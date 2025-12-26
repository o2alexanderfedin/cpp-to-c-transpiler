// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/runtime_mode_library_test.cpp
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
struct RuntimeModeLibrary {
	int usedFeatures_;
};
static void RuntimeModeLibrary__ctor_copy(struct RuntimeModeLibrary * this, const struct RuntimeModeLibrary * other);
int TEST(int, int);
void RuntimeModeLibrary_markFeatureUsed(struct RuntimeModeLibrary * this, RuntimeFeature feature);
int TEST_int_int(int, int);
int TEST_int_int_1(int, int);
int TEST_int_int_2(int, int);
int TEST_int_int_3(int, int);
int TEST_int_int_4(int, int);
int TEST_int_int_5(int, int);
int TEST_int_int_6(int, int);
int TEST_int_int_7(int, int);
int TEST_int_int_8(int, int);
int TEST_int_int_9(int, int);
int TEST_int_int_10(int, int);
