// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/CallingConventionTest.cpp
// Implementation file

#include "CallingConventionTest.h"

int buildAST(const char * code) {
}

int * findFunction(int * Ctx, const int * name) {
	return nullptr;
;
}

int getCallingConv(int * FD) {
	const int *FT;

}

static void CallingConventionTest__ctor_default(struct CallingConventionTest * this) {
}

static void CallingConventionTest__ctor_copy(struct CallingConventionTest * this, const struct CallingConventionTest * other) {
}

int TEST_F(struct CallingConventionTest, int) {
	const char *code = "\n            void normalFunc(int x) {}\n        ";

	int *FD;

}

int TEST_F_CallingConventionTest_int(struct CallingConventionTest, int) {
	const char *code = "\n            void func1(int x) {}\n            void __attribute__((ms_abi)) func2(int x) {}\n        ";

	int *func1;

	int cc1;

}

int TEST_F_CallingConventionTest_int_1(struct CallingConventionTest, int) {
	const char *code = "\n            extern \"C\" void exported(int x) {}\n        ";

	int *FD;

	int CC;

}

