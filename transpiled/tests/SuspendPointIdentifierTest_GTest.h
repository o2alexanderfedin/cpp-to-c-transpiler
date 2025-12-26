// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/SuspendPointIdentifierTest_GTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct SuspendPoint {
	int kind;
	unsigned int line;
	unsigned int column;
	unsigned int stateId;
	const int * stmt;
};
static void SuspendPoint__ctor_default(struct SuspendPoint * this);
static void SuspendPoint__ctor_copy(struct SuspendPoint * this, const struct SuspendPoint * other);
struct SuspendPointIdentifier {
	int & Context;
};
static void SuspendPointIdentifier__ctor_default(struct SuspendPointIdentifier * this);
static void SuspendPointIdentifier__ctor_copy(struct SuspendPointIdentifier * this, const struct SuspendPointIdentifier * other);
struct SuspendPointIdentifierTestFixture {
};
static void SuspendPointIdentifierTestFixture__ctor_default(struct SuspendPointIdentifierTestFixture * this);
static void SuspendPointIdentifierTestFixture__ctor_copy(struct SuspendPointIdentifierTestFixture * this, const struct SuspendPointIdentifierTestFixture * other);
int SuspendPointIdentifierTestFixture_buildAST(struct SuspendPointIdentifierTestFixture * this, const char * code);
int * SuspendPointIdentifierTestFixture_findFunction(struct SuspendPointIdentifierTestFixture * this, int * TU, const int * name);
int TEST_F(struct SuspendPointIdentifierTestFixture, int);
int TEST_F_SuspendPointIdentifierTestFixture_int(struct SuspendPointIdentifierTestFixture, int);
int TEST_F_SuspendPointIdentifierTestFixture_int_1(struct SuspendPointIdentifierTestFixture, int);
int TEST_F_SuspendPointIdentifierTestFixture_int_2(struct SuspendPointIdentifierTestFixture, int);
int TEST_F_SuspendPointIdentifierTestFixture_int_3(struct SuspendPointIdentifierTestFixture, int);
int TEST_F_SuspendPointIdentifierTestFixture_int_4(struct SuspendPointIdentifierTestFixture, int);
int TEST_F_SuspendPointIdentifierTestFixture_int_5(struct SuspendPointIdentifierTestFixture, int);
