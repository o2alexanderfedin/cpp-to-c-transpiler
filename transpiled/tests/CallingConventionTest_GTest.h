// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/CallingConventionTest_GTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct CallingConventionTestFixture {
};
static void CallingConventionTestFixture__ctor_default(struct CallingConventionTestFixture * this);
static void CallingConventionTestFixture__ctor_copy(struct CallingConventionTestFixture * this, const struct CallingConventionTestFixture * other);
int CallingConventionTestFixture_buildAST(struct CallingConventionTestFixture * this, const char * code);
int * CallingConventionTestFixture_findFunction(struct CallingConventionTestFixture * this, int * Ctx, const int * name);
int CallingConventionTestFixture_getCallingConv(struct CallingConventionTestFixture * this, int * FD);
int TEST_F(struct CallingConventionTestFixture, int);
int TEST_F_CallingConventionTestFixture_int(struct CallingConventionTestFixture, int);
int TEST_F_CallingConventionTestFixture_int_1(struct CallingConventionTestFixture, int);
