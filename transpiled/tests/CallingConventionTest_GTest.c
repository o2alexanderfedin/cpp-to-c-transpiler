// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/CallingConventionTest_GTest.cpp
// Implementation file

#include "CallingConventionTest_GTest.h"

static void CallingConventionTestFixture__ctor_default(struct CallingConventionTestFixture * this) {
}

static void CallingConventionTestFixture__ctor_copy(struct CallingConventionTestFixture * this, const struct CallingConventionTestFixture * other) {
}

int CallingConventionTestFixture_buildAST(struct CallingConventionTestFixture * this, const char * code) {
}

int * CallingConventionTestFixture_findFunction(struct CallingConventionTestFixture * this, int * Ctx, const int * name) {
	return nullptr;
;
}

int CallingConventionTestFixture_getCallingConv(struct CallingConventionTestFixture * this, int * FD) {
	const int *FT;

}

int TEST_F(struct CallingConventionTestFixture, int) {
	const char *code = "\n        void normalFunc(int x) {}\n    ";

	int *FD;

}

int TEST_F_CallingConventionTestFixture_int(struct CallingConventionTestFixture, int) {
	const char *code = "\n        void func1(int x) {}\n        void __attribute__((ms_abi)) func2(int x) {}\n    ";

	int *func1;

	int cc1;

}

int TEST_F_CallingConventionTestFixture_int_1(struct CallingConventionTestFixture, int) {
	const char *code = "\n        extern \"C\" void exported(int x) {}\n    ";

	int *FD;

	int CC;

}

