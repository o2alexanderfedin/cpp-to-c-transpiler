// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/FileOutputManagerTest_GTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

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
struct FileOutputManagerTestFixture {
};
static void FileOutputManagerTestFixture__ctor_default(struct FileOutputManagerTestFixture * this);
static void FileOutputManagerTestFixture__ctor_copy(struct FileOutputManagerTestFixture * this, const struct FileOutputManagerTestFixture * other);
bool FileOutputManagerTestFixture_fileExists(struct FileOutputManagerTestFixture * this, const int * filename);
void FileOutputManagerTestFixture_TearDown(struct FileOutputManagerTestFixture * this);
int TEST_F(struct FileOutputManagerTestFixture, int);
int TEST_F_FileOutputManagerTestFixture_int(struct FileOutputManagerTestFixture, int);
int TEST_F_FileOutputManagerTestFixture_int_1(struct FileOutputManagerTestFixture, int);
int TEST_F_FileOutputManagerTestFixture_int_2(struct FileOutputManagerTestFixture, int);
int TEST_F_FileOutputManagerTestFixture_int_3(struct FileOutputManagerTestFixture, int);
