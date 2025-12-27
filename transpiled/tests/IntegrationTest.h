// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/IntegrationTest.cpp
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
struct IncludeGuardGenerator {
	bool m_usePragmaOnce;
};
static void IncludeGuardGenerator__ctor_copy(struct IncludeGuardGenerator * this, const struct IncludeGuardGenerator * other);
struct DependencyAnalyzer {
	int ownHeader;
	int runtimeDeps;
};
static void DependencyAnalyzer__ctor_default(struct DependencyAnalyzer * this);
static void DependencyAnalyzer__ctor_copy(struct DependencyAnalyzer * this, const struct DependencyAnalyzer * other);
struct FileOutputManager {
	int inputFilename;
	int outputDir;
	int outputHeader;
	int outputImpl;
	int sourceDir;
};
static void FileOutputManager__ctor_default(struct FileOutputManager * this);
static void FileOutputManager__ctor_copy(struct FileOutputManager * this, const struct FileOutputManager * other);
struct FileContent {
	int originFile;
	int headerContent;
	int implContent;
};
static void FileContent__ctor_default(struct FileContent * this);
static void FileContent__ctor_copy(struct FileContent * this, const struct FileContent * other);
int TEST(int, int);
int TEST_int_int(int, int);
int TEST_int_int_1(int, int);
int TEST_int_int_2(int, int);
int TEST_int_int_3(int, int);
