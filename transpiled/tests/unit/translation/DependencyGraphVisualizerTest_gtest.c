// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/translation/DependencyGraphVisualizerTest_gtest.cpp
// Implementation file

#include "DependencyGraphVisualizerTest_gtest.h"

static void DependencyGraphVisualizer__ctor_copy(struct DependencyGraphVisualizer * this, const struct DependencyGraphVisualizer * other) {
}

static void DependencyGraphVisualizerTestFixture__ctor_default(struct DependencyGraphVisualizerTestFixture * this) {
}

static void DependencyGraphVisualizerTestFixture__ctor_copy(struct DependencyGraphVisualizerTestFixture * this, const struct DependencyGraphVisualizerTestFixture * other) {
}

void DependencyGraphVisualizerTestFixture_SetUp(struct DependencyGraphVisualizerTestFixture * this) {
}

void DependencyGraphVisualizerTestFixture_TearDown(struct DependencyGraphVisualizerTestFixture * this) {
}

int TEST_F(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	int dot;

}

int TEST_F_DependencyGraphVisualizerTestFixture_int(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto files = viz()();

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_1(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto files = viz()();

	auto deps = viz()("Point.c");

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_2(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto files = viz()();

	auto circleDeps = viz()("Circle.c");

	auto circleHDeps = viz()("Circle.h");

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_3(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto dot = viz()();

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_4(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto cycles = viz()();

	bool foundCycle = false;

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_5(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto cycles = viz()();

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_6(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto cycles = viz()();

	bool foundCycle = false;

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_7(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	int dot;

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_8(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	int dot;

}

void DependencyGraphVisualizer_clear(struct DependencyGraphVisualizer * this);
int TEST_F_DependencyGraphVisualizerTestFixture_int_9(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	DependencyGraphVisualizer_clear(&viz);
}

int TEST_F_DependencyGraphVisualizerTestFixture_int_10(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	int filename;

	bool success;

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_11(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto files = viz()();

	auto cycles = viz()();

	int dot;

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_12(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto cycles = viz()();

}

int TEST_F_DependencyGraphVisualizerTestFixture_int_13(struct DependencyGraphVisualizerTestFixture, int) {
	struct DependencyGraphVisualizer viz;

	auto files = viz()();

}

