// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/DependencyAnalyzerTest_GTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct DependencyAnalyzer {
	int ownHeader;
	int runtimeDeps;
};
static void DependencyAnalyzer__ctor_default(struct DependencyAnalyzer * this);
static void DependencyAnalyzer__ctor_copy(struct DependencyAnalyzer * this, const struct DependencyAnalyzer * other);
struct DependencyAnalyzerTestFixture {
};
static void DependencyAnalyzerTestFixture__ctor_default(struct DependencyAnalyzerTestFixture * this);
static void DependencyAnalyzerTestFixture__ctor_copy(struct DependencyAnalyzerTestFixture * this, const struct DependencyAnalyzerTestFixture * other);
int TEST_F(struct DependencyAnalyzerTestFixture, int);
int TEST_F_DependencyAnalyzerTestFixture_int(struct DependencyAnalyzerTestFixture, int);
int TEST_F_DependencyAnalyzerTestFixture_int_1(struct DependencyAnalyzerTestFixture, int);
int TEST_F_DependencyAnalyzerTestFixture_int_2(struct DependencyAnalyzerTestFixture, int);
int TEST_F_DependencyAnalyzerTestFixture_int_3(struct DependencyAnalyzerTestFixture, int);
