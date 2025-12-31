// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/operators/OperatorOverloadingTest.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct OperatorOverloadingTestBase {
};
static void OperatorOverloadingTestBase__ctor_default(struct OperatorOverloadingTestBase * this);
static void OperatorOverloadingTestBase__ctor_copy(struct OperatorOverloadingTestBase * this, const struct OperatorOverloadingTestBase * other);
int OperatorOverloadingTestBase_buildAST_const_int_ptr(struct OperatorOverloadingTestBase * this, const char * code);
struct ArithmeticOperatorTest {
};
static void ArithmeticOperatorTest__ctor_default(struct ArithmeticOperatorTest * this);
static void ArithmeticOperatorTest__ctor_copy(struct ArithmeticOperatorTest * this, const struct ArithmeticOperatorTest * other);
int TEST_F(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_1(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_2(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_3(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_4(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_5(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_6(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_7(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_8(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_9(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_10(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_11(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_12(struct ArithmeticOperatorTest, int);
int TEST_F_ArithmeticOperatorTest_int_13(struct ArithmeticOperatorTest, int);
struct ComparisonOperatorTest {
};
static void ComparisonOperatorTest__ctor_default(struct ComparisonOperatorTest * this);
static void ComparisonOperatorTest__ctor_copy(struct ComparisonOperatorTest * this, const struct ComparisonOperatorTest * other);
int TEST_F_ComparisonOperatorTest_int(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_1(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_2(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_3(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_4(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_5(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_6(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_7(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_8(struct ComparisonOperatorTest, int);
int TEST_F_ComparisonOperatorTest_int_9(struct ComparisonOperatorTest, int);
struct SubscriptCallOperatorTest {
};
static void SubscriptCallOperatorTest__ctor_default(struct SubscriptCallOperatorTest * this);
static void SubscriptCallOperatorTest__ctor_copy(struct SubscriptCallOperatorTest * this, const struct SubscriptCallOperatorTest * other);
int TEST_F_SubscriptCallOperatorTest_int(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_1(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_2(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_3(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_4(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_5(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_6(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_7(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_8(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_9(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_10(struct SubscriptCallOperatorTest, int);
int TEST_F_SubscriptCallOperatorTest_int_11(struct SubscriptCallOperatorTest, int);
struct SpecialOperatorTest {
};
static void SpecialOperatorTest__ctor_default(struct SpecialOperatorTest * this);
static void SpecialOperatorTest__ctor_copy(struct SpecialOperatorTest * this, const struct SpecialOperatorTest * other);
int TEST_F_SpecialOperatorTest_int(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_1(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_2(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_3(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_4(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_5(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_6(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_7(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_8(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_9(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_10(struct SpecialOperatorTest, int);
int TEST_F_SpecialOperatorTest_int_11(struct SpecialOperatorTest, int);
struct ConversionOperatorTest {
};
static void ConversionOperatorTest__ctor_default(struct ConversionOperatorTest * this);
static void ConversionOperatorTest__ctor_copy(struct ConversionOperatorTest * this, const struct ConversionOperatorTest * other);
int TEST_F_ConversionOperatorTest_int(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_1(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_2(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_3(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_4(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_5(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_6(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_7(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_8(struct ConversionOperatorTest, int);
int TEST_F_ConversionOperatorTest_int_9(struct ConversionOperatorTest, int);
struct StreamOperatorTest {
};
static void StreamOperatorTest__ctor_default(struct StreamOperatorTest * this);
static void StreamOperatorTest__ctor_copy(struct StreamOperatorTest * this, const struct StreamOperatorTest * other);
int TEST_F_StreamOperatorTest_int(struct StreamOperatorTest, int);
int TEST_F_StreamOperatorTest_int_1(struct StreamOperatorTest, int);
int TEST_F_StreamOperatorTest_int_2(struct StreamOperatorTest, int);
