// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ForwardDeclTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct HeaderSeparator {
	int headerDecls;
	int implDecls;
	int forwardDecls;
};
static void HeaderSeparator__ctor_default(struct HeaderSeparator * this);
static void HeaderSeparator__ctor_copy(struct HeaderSeparator * this, const struct HeaderSeparator * other);
const int * HeaderSeparator_getHeaderDecls(struct HeaderSeparator * this);
const int * HeaderSeparator_getImplDecls(struct HeaderSeparator * this);
const int * HeaderSeparator_getForwardDecls(struct HeaderSeparator * this);
int TEST(int, int);
int TEST_int_int(int, int);
int TEST_int_int_1(int, int);
int TEST_int_int_2(int, int);
int TEST_int_int_3(int, int);
int TEST_int_int_4(int, int);
