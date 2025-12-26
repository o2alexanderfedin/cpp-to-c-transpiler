// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/runtime_mode_library_test.cpp
// Implementation file

#include "runtime_mode_library_test.h"

static void RuntimeModeLibrary__ctor_copy(struct RuntimeModeLibrary * this, const struct RuntimeModeLibrary * other) {
	this->usedFeatures_ = other->usedFeatures_;
}

int TEST(int, int) {
	struct RuntimeModeLibrary libraryMode;

}

void RuntimeModeLibrary_markFeatureUsed(struct RuntimeModeLibrary * this, RuntimeFeature feature);
int TEST_int_int(int, int) {
	struct RuntimeModeLibrary libraryMode;

	RuntimeModeLibrary_markFeatureUsed(&libraryMode, 0);
	int headerCode;

}

int TEST_int_int_1(int, int) {
	struct RuntimeModeLibrary libraryMode;

	RuntimeModeLibrary_markFeatureUsed(&libraryMode, 1);
	int headerCode;

}

int TEST_int_int_2(int, int) {
	struct RuntimeModeLibrary libraryMode;

	RuntimeModeLibrary_markFeatureUsed(&libraryMode, 0);
	int headerCode;

}

int TEST_int_int_3(int, int) {
	struct RuntimeModeLibrary libraryMode;

	RuntimeModeLibrary_markFeatureUsed(&libraryMode, 0);
	int generatedCode;

}

int TEST_int_int_4(int, int) {
	struct RuntimeModeLibrary libraryMode;

	int linkFlags;

}

int TEST_int_int_5(int, int) {
	struct RuntimeModeLibrary libraryMode;

	int cmakeCode;

}

int TEST_int_int_6(int, int) {
	struct RuntimeModeLibrary libraryMode;

	int numFiles = 100;

	RuntimeModeLibrary_markFeatureUsed(&libraryMode, 0);
	RuntimeModeLibrary_markFeatureUsed(&libraryMode, 1);
	int inlineSize;

	int librarySize;

	double reduction;
}

int TEST_int_int_7(int, int) {
	struct RuntimeModeLibrary libraryMode;

	int numFiles = 100;

	double inlineTime = numFiles * 1.;

	double libraryTime = numFiles * 0.72999999999999998;

	double improvement = ((inlineTime - libraryTime) / inlineTime) * 100.;

}

int TEST_int_int_8(int, int) {
	struct RuntimeModeLibrary libraryMode;

	RuntimeModeLibrary_markFeatureUsed(&libraryMode, 0);
	int headerCode;

}

int TEST_int_int_9(int, int) {
	struct RuntimeModeLibrary libraryMode;

	int version;

}

int TEST_int_int_10(int, int) {
	struct RuntimeModeLibrary libraryMode;

	RuntimeModeLibrary_markFeatureUsed(&libraryMode, 0);
	int header;

}

