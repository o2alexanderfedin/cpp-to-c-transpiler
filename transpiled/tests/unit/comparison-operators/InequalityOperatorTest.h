// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/comparison-operators/InequalityOperatorTest.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct InequalityOperatorTestBase {
};
static void InequalityOperatorTestBase__ctor_default(struct InequalityOperatorTestBase * this);
static void InequalityOperatorTestBase__ctor_copy(struct InequalityOperatorTestBase * this, const struct InequalityOperatorTestBase * other);
int InequalityOperatorTestBase_buildAST_const_int_ptr(struct InequalityOperatorTestBase * this, const char * code);
struct InequalityOperatorTest {
};
static void InequalityOperatorTest__ctor_default(struct InequalityOperatorTest * this);
static void InequalityOperatorTest__ctor_copy(struct InequalityOperatorTest * this, const struct InequalityOperatorTest * other);
int TEST_F(struct InequalityOperatorTest, int);
int TEST_F_InequalityOperatorTest_int(struct InequalityOperatorTest, int);
int TEST_F_InequalityOperatorTest_int_1(struct InequalityOperatorTest, int);
int TEST_F_InequalityOperatorTest_int_2(struct InequalityOperatorTest, int);
int TEST_F_InequalityOperatorTest_int_3(struct InequalityOperatorTest, int);
int TEST_F_InequalityOperatorTest_int_4(struct InequalityOperatorTest, int);
int TEST_F_InequalityOperatorTest_int_5(struct InequalityOperatorTest, int);
struct OperatorCallFinder {
	bool found;
};
static void OperatorCallFinder__ctor_default(struct OperatorCallFinder * this);
static void OperatorCallFinder__ctor_copy(struct OperatorCallFinder * this, const struct OperatorCallFinder * other);
bool OperatorCallFinder_VisitCXXOperatorCallExpr_int_ptr(struct OperatorCallFinder * this, int * OCE);
int TEST_F_InequalityOperatorTest_int_6(struct InequalityOperatorTest, int);
struct InequalityAdvancedTest {
};
static void InequalityAdvancedTest__ctor_default(struct InequalityAdvancedTest * this);
static void InequalityAdvancedTest__ctor_copy(struct InequalityAdvancedTest * this, const struct InequalityAdvancedTest * other);
int TEST_F_InequalityAdvancedTest_int(struct InequalityAdvancedTest, int);
int TEST_F_InequalityAdvancedTest_int_1(struct InequalityAdvancedTest, int);
