// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/MoveConstructorTranslationTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct MoveConstructorTranslator {
	int & Context;
};
static void MoveConstructorTranslator__ctor_default(struct MoveConstructorTranslator * this);
static void MoveConstructorTranslator__ctor_copy(struct MoveConstructorTranslator * this, const struct MoveConstructorTranslator * other);
int buildAST(const char * code);
struct MoveConstructorFinder {
	int moveConstructors;
};
static void MoveConstructorFinder__ctor_default(struct MoveConstructorFinder * this);
static void MoveConstructorFinder__ctor_copy(struct MoveConstructorFinder * this, const struct MoveConstructorFinder * other);
bool MoveConstructorFinder_VisitCXXConstructorDecl(struct MoveConstructorFinder * this, int * D);
struct MoveConstructorTranslationTest {
};
static void MoveConstructorTranslationTest__ctor_default(struct MoveConstructorTranslationTest * this);
static void MoveConstructorTranslationTest__ctor_copy(struct MoveConstructorTranslationTest * this, const struct MoveConstructorTranslationTest * other);
int TEST_F(struct MoveConstructorTranslationTest, int);
int TEST_F_MoveConstructorTranslationTest_int(struct MoveConstructorTranslationTest, int);
int TEST_F_MoveConstructorTranslationTest_int_1(struct MoveConstructorTranslationTest, int);
int TEST_F_MoveConstructorTranslationTest_int_2(struct MoveConstructorTranslationTest, int);
int TEST_F_MoveConstructorTranslationTest_int_3(struct MoveConstructorTranslationTest, int);
int TEST_F_MoveConstructorTranslationTest_int_4(struct MoveConstructorTranslationTest, int);
int TEST_F_MoveConstructorTranslationTest_int_5(struct MoveConstructorTranslationTest, int);
