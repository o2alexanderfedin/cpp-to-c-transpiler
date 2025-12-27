// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/RvalueRefParameterTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct RvalueRefParamTranslator {
	int & Context;
};
static void RvalueRefParamTranslator__ctor_default(struct RvalueRefParamTranslator * this);
static void RvalueRefParamTranslator__ctor_copy(struct RvalueRefParamTranslator * this, const struct RvalueRefParamTranslator * other);
int buildAST(const char * code);
struct FunctionFinder {
	int functions;
	int rvalueRefParams;
};
static void FunctionFinder__ctor_default(struct FunctionFinder * this);
static void FunctionFinder__ctor_copy(struct FunctionFinder * this, const struct FunctionFinder * other);
bool FunctionFinder_VisitFunctionDecl(struct FunctionFinder * this, const int * FD);
struct RvalueRefParameterTest {
};
static void RvalueRefParameterTest__ctor_default(struct RvalueRefParameterTest * this);
static void RvalueRefParameterTest__ctor_copy(struct RvalueRefParameterTest * this, const struct RvalueRefParameterTest * other);
int TEST_F(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int_1(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int_2(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int_3(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int_4(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int_5(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int_6(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int_7(struct RvalueRefParameterTest, int);
int TEST_F_RvalueRefParameterTest_int_8(struct RvalueRefParameterTest, int);
