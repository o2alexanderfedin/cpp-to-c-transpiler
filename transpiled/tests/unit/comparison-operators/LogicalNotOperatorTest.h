// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/comparison-operators/LogicalNotOperatorTest.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct LogicalNotOperatorTestBase {
};
static void LogicalNotOperatorTestBase__ctor_default(struct LogicalNotOperatorTestBase * this);
static void LogicalNotOperatorTestBase__ctor_copy(struct LogicalNotOperatorTestBase * this, const struct LogicalNotOperatorTestBase * other);
int LogicalNotOperatorTestBase_buildAST_const_int_ptr(struct LogicalNotOperatorTestBase * this, const char * code);
struct LogicalNotOperatorTest {
};
static void LogicalNotOperatorTest__ctor_default(struct LogicalNotOperatorTest * this);
static void LogicalNotOperatorTest__ctor_copy(struct LogicalNotOperatorTest * this, const struct LogicalNotOperatorTest * other);
int TEST_F(struct LogicalNotOperatorTest, int);
int TEST_F_LogicalNotOperatorTest_int(struct LogicalNotOperatorTest, int);
int TEST_F_LogicalNotOperatorTest_int_1(struct LogicalNotOperatorTest, int);
int TEST_F_LogicalNotOperatorTest_int_2(struct LogicalNotOperatorTest, int);
int TEST_F_LogicalNotOperatorTest_int_3(struct LogicalNotOperatorTest, int);
int TEST_F_LogicalNotOperatorTest_int_4(struct LogicalNotOperatorTest, int);
int TEST_F_LogicalNotOperatorTest_int_5(struct LogicalNotOperatorTest, int);
int TEST_F_LogicalNotOperatorTest_int_6(struct LogicalNotOperatorTest, int);
struct LogicalNotOperatorNonConstTest {
};
static void LogicalNotOperatorNonConstTest__ctor_default(struct LogicalNotOperatorNonConstTest * this);
static void LogicalNotOperatorNonConstTest__ctor_copy(struct LogicalNotOperatorNonConstTest * this, const struct LogicalNotOperatorNonConstTest * other);
int TEST_F_LogicalNotOperatorNonConstTest_int(struct LogicalNotOperatorNonConstTest, int);
