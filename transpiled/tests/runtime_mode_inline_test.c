// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/runtime_mode_inline_test.cpp
// Implementation file

#include "runtime_mode_inline_test.h"

static void RuntimeModeInline__ctor_copy(struct RuntimeModeInline * this, const struct RuntimeModeInline * other) {
	this->usedFeatures_ = other->usedFeatures_;
}

int TEST(int, int mode) {
	struct RuntimeModeInline inlineMode;

}

int TEST_int_int(int, int runtime) {
	struct RuntimeModeInline inlineMode;

	int embeddedCode;

}

int TEST_int_int_1(int, int runtime) {
	struct RuntimeModeInline inlineMode;

	int embeddedCode;

}

int TEST_int_int_2(int, int runtime) {
	struct RuntimeModeInline inlineMode;

	int embeddedCode;

}

int TEST_int_int_3(int, int inheritance) {
	struct RuntimeModeInline inlineMode;

	int embeddedCode;

}

void RuntimeModeInline_markFeatureUsed(struct RuntimeModeInline * this, RuntimeFeature feature);
int TEST_int_int_4(int, int compilation) {
	struct RuntimeModeInline inlineMode;

	RuntimeModeInline_markFeatureUsed(&inlineMode, 0);
	int embeddedCode;

}

int TEST_int_int_5(int, int features) {
	struct RuntimeModeInline inlineMode;

	RuntimeModeInline_markFeatureUsed(&inlineMode, 0);
	RuntimeModeInline_markFeatureUsed(&inlineMode, 1);
	int embeddedCode;

}

int TEST_int_int_6(int, int guards) {
	struct RuntimeModeInline inlineMode;

	RuntimeModeInline_markFeatureUsed(&inlineMode, 0);
	int embeddedCode;

	int firstGuard;

	int defineGuard;

	int endifGuard;

}

int TEST_int_int_7(int, int transpilation) {
	const char *cppCode = "\n            void test() {\n                try {\n                    throw 42;\n                } catch (int e) {\n                    // handle\n                }\n            }\n        ";

	struct RuntimeModeInline inlineMode;

	RuntimeModeInline_markFeatureUsed(&inlineMode, 0);
	int runtime;

}

