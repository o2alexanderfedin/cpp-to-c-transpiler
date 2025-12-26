// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/StdMoveTranslationTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct StdMoveTranslator {
	int & Context;
};
static void StdMoveTranslator__ctor_default(struct StdMoveTranslator * this);
static void StdMoveTranslator__ctor_copy(struct StdMoveTranslator * this, const struct StdMoveTranslator * other);
typedef enum {
    Construction = 0,
    Assignment = 1,
    Argument = 2,
    Return = 3
} MoveContext;
int buildAST(const char * code);
struct StdMoveFinder {
	int moveCallExprs;
};
static void StdMoveFinder__ctor_default(struct StdMoveFinder * this);
static void StdMoveFinder__ctor_copy(struct StdMoveFinder * this, const struct StdMoveFinder * other);
bool StdMoveFinder_VisitCallExpr(struct StdMoveFinder * this, const int * Call);
struct StdMoveTranslationTest {
};
static void StdMoveTranslationTest__ctor_default(struct StdMoveTranslationTest * this);
static void StdMoveTranslationTest__ctor_copy(struct StdMoveTranslationTest * this, const struct StdMoveTranslationTest * other);
int TEST_F(struct StdMoveTranslationTest, int);
int TEST_F_StdMoveTranslationTest_int(struct StdMoveTranslationTest, int);
int TEST_F_StdMoveTranslationTest_int_1(struct StdMoveTranslationTest, int);
int TEST_F_StdMoveTranslationTest_int_2(struct StdMoveTranslationTest, int);
int TEST_F_StdMoveTranslationTest_int_3(struct StdMoveTranslationTest, int);
