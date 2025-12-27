// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/RuntimeIntegrationTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct RuntimeIntegrationTest {
	int harness;
};
static void RuntimeIntegrationTest__ctor_default(struct RuntimeIntegrationTest * this);
static void RuntimeIntegrationTest__ctor_copy(struct RuntimeIntegrationTest * this, const struct RuntimeIntegrationTest * other);
void RuntimeIntegrationTest_SetUp(struct RuntimeIntegrationTest * this);
void RuntimeIntegrationTest_TearDown(struct RuntimeIntegrationTest * this);
void RuntimeIntegrationTest_assertCompiles(struct RuntimeIntegrationTest * this, const int * c_code);
void RuntimeIntegrationTest_assertTranspiledRuns(struct RuntimeIntegrationTest * this, const int * cpp_code, const int * expected_output);
void RuntimeIntegrationTest_assertOutputMatches(struct RuntimeIntegrationTest * this, const int * result, const int * regex_pattern);
int TEST_F(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_1(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_2(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_3(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_4(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_5(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_6(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_7(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_8(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_9(struct RuntimeIntegrationTest, int);
int TEST_F_RuntimeIntegrationTest_int_10(struct RuntimeIntegrationTest, int);
