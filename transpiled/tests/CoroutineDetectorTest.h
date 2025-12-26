// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/CoroutineDetectorTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct LocalVariableInfo {
	int name;
	int type;
	const int * decl;
};
static void LocalVariableInfo__ctor_default(struct LocalVariableInfo * this);
static void LocalVariableInfo__ctor_copy(struct LocalVariableInfo * this, const struct LocalVariableInfo * other);
void LocalVariableInfo__ctor(struct LocalVariableInfo * this, const int * n, const int * t, const int * d);
struct CoroutineDetector {
	int & Context;
};
static void CoroutineDetector__ctor_default(struct CoroutineDetector * this);
static void CoroutineDetector__ctor_copy(struct CoroutineDetector * this, const struct CoroutineDetector * other);
int buildAST(const char * code);
int * findFunction(int * TU, const int * name);
struct CoroutineDetectorTest {
};
static void CoroutineDetectorTest__ctor_default(struct CoroutineDetectorTest * this);
static void CoroutineDetectorTest__ctor_copy(struct CoroutineDetectorTest * this, const struct CoroutineDetectorTest * other);
int TEST_F(struct CoroutineDetectorTest, int);
