// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/CallingConventionTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

int buildAST(const char * code);
int * findFunction(int * Ctx, const int * name);
int getCallingConv(int * FD);
struct CallingConventionTest {
};
static void CallingConventionTest__ctor_default(struct CallingConventionTest * this);
static void CallingConventionTest__ctor_copy(struct CallingConventionTest * this, const struct CallingConventionTest * other);
int TEST_F(struct CallingConventionTest, int);
int TEST_F_CallingConventionTest_int(struct CallingConventionTest, int);
int TEST_F_CallingConventionTest_int_1(struct CallingConventionTest, int);
