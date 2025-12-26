// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/MoveAssignmentTranslationTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct MoveAssignmentTranslator {
	int & Context;
};
static void MoveAssignmentTranslator__ctor_default(struct MoveAssignmentTranslator * this);
static void MoveAssignmentTranslator__ctor_copy(struct MoveAssignmentTranslator * this, const struct MoveAssignmentTranslator * other);
int buildAST(const char * code);
struct MoveAssignmentFinder {
	int moveAssignmentOperators;
};
static void MoveAssignmentFinder__ctor_default(struct MoveAssignmentFinder * this);
static void MoveAssignmentFinder__ctor_copy(struct MoveAssignmentFinder * this, const struct MoveAssignmentFinder * other);
bool MoveAssignmentFinder_VisitCXXMethodDecl(struct MoveAssignmentFinder * this, int * D);
struct MoveAssignmentTranslationTest {
};
static void MoveAssignmentTranslationTest__ctor_default(struct MoveAssignmentTranslationTest * this);
static void MoveAssignmentTranslationTest__ctor_copy(struct MoveAssignmentTranslationTest * this, const struct MoveAssignmentTranslationTest * other);
int TEST_F(struct MoveAssignmentTranslationTest, int);
int TEST_F_MoveAssignmentTranslationTest_int(struct MoveAssignmentTranslationTest, int);
int TEST_F_MoveAssignmentTranslationTest_int_1(struct MoveAssignmentTranslationTest, int);
int TEST_F_MoveAssignmentTranslationTest_int_2(struct MoveAssignmentTranslationTest, int);
int TEST_F_MoveAssignmentTranslationTest_int_3(struct MoveAssignmentTranslationTest, int);
int TEST_F_MoveAssignmentTranslationTest_int_4(struct MoveAssignmentTranslationTest, int);
int TEST_F_MoveAssignmentTranslationTest_int_5(struct MoveAssignmentTranslationTest, int);
int TEST_F_MoveAssignmentTranslationTest_int_6(struct MoveAssignmentTranslationTest, int);
int TEST_F_MoveAssignmentTranslationTest_int_7(struct MoveAssignmentTranslationTest, int);
