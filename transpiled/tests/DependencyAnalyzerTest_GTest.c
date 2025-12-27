// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/DependencyAnalyzerTest_GTest.cpp
// Implementation file

#include "DependencyAnalyzerTest_GTest.h"

static void DependencyAnalyzer__ctor_default(struct DependencyAnalyzer * this) {
	this->ownHeader = 0;
	this->runtimeDeps = 0;
}

static void DependencyAnalyzer__ctor_copy(struct DependencyAnalyzer * this, const struct DependencyAnalyzer * other) {
	this->ownHeader = other->ownHeader;
	this->runtimeDeps = other->runtimeDeps;
}

static void DependencyAnalyzerTestFixture__ctor_default(struct DependencyAnalyzerTestFixture * this) {
}

static void DependencyAnalyzerTestFixture__ctor_copy(struct DependencyAnalyzerTestFixture * this, const struct DependencyAnalyzerTestFixture * other) {
}

int TEST_F(struct DependencyAnalyzerTestFixture, int) {
	struct DependencyAnalyzer analyzer;

	auto includes = analyzer()();

}

int TEST_F_DependencyAnalyzerTestFixture_int(struct DependencyAnalyzerTestFixture, int) {
	struct DependencyAnalyzer analyzer;

	auto includes = analyzer()();

}

int TEST_F_DependencyAnalyzerTestFixture_int_1(struct DependencyAnalyzerTestFixture, int) {
	struct DependencyAnalyzer analyzer;

	int includeDirectives;

}

int TEST_F_DependencyAnalyzerTestFixture_int_2(struct DependencyAnalyzerTestFixture, int) {
	struct DependencyAnalyzer analyzer;

	auto includes1 = analyzer()();

	auto includes2 = analyzer()();

}

int TEST_F_DependencyAnalyzerTestFixture_int_3(struct DependencyAnalyzerTestFixture, int) {
	struct DependencyAnalyzer analyzer;

	auto includes = analyzer()();

}

