// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ActionTableGeneratorTest_GTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct TryBlockInfo {
	int * tryStmt;
	int constructedObjects;
	int tryBlockIndex;
};
static void TryBlockInfo__ctor_default(struct TryBlockInfo * this);
static void TryBlockInfo__ctor_copy(struct TryBlockInfo * this, const struct TryBlockInfo * other);
struct ActionTableGenerator {
	int tryBlocks;
};
static void ActionTableGenerator__ctor_copy(struct ActionTableGenerator * this, const struct ActionTableGenerator * other);
int ActionTableGenerator_getTryBlockCount(struct ActionTableGenerator * this);
const int * ActionTableGenerator_getTryBlocks(struct ActionTableGenerator * this);
struct ActionTableGeneratorTestFixture {
};
static void ActionTableGeneratorTestFixture__ctor_default(struct ActionTableGeneratorTestFixture * this);
static void ActionTableGeneratorTestFixture__ctor_copy(struct ActionTableGeneratorTestFixture * this, const struct ActionTableGeneratorTestFixture * other);
int * ActionTableGeneratorTestFixture_findFunction(struct ActionTableGeneratorTestFixture * this, int * TU, const int * name);
int TEST_F(struct ActionTableGeneratorTestFixture, int);
int TEST_F_ActionTableGeneratorTestFixture_int(struct ActionTableGeneratorTestFixture, int);
int TEST_F_ActionTableGeneratorTestFixture_int_1(struct ActionTableGeneratorTestFixture, int);
int TEST_F_ActionTableGeneratorTestFixture_int_2(struct ActionTableGeneratorTestFixture, int);
int TEST_F_ActionTableGeneratorTestFixture_int_3(struct ActionTableGeneratorTestFixture, int);
int TEST_F_ActionTableGeneratorTestFixture_int_4(struct ActionTableGeneratorTestFixture, int);
int TEST_F_ActionTableGeneratorTestFixture_int_5(struct ActionTableGeneratorTestFixture, int);
int TEST_F_ActionTableGeneratorTestFixture_int_6(struct ActionTableGeneratorTestFixture, int);
int TEST_F_ActionTableGeneratorTestFixture_int_7(struct ActionTableGeneratorTestFixture, int);
