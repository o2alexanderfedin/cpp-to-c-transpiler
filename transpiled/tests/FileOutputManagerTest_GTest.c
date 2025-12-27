// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/FileOutputManagerTest_GTest.cpp
// Implementation file

#include "FileOutputManagerTest_GTest.h"

static void FileOutputManager__ctor_default(struct FileOutputManager * this) {
	this->inputFilename = 0;
	this->outputDir = 0;
	this->outputHeader = 0;
	this->outputImpl = 0;
	this->sourceDir = 0;
}

static void FileOutputManager__ctor_copy(struct FileOutputManager * this, const struct FileOutputManager * other) {
	this->inputFilename = other->inputFilename;
	this->outputDir = other->outputDir;
	this->outputHeader = other->outputHeader;
	this->outputImpl = other->outputImpl;
	this->sourceDir = other->sourceDir;
}

static void FileContent__ctor_default(struct FileContent * this) {
	this->originFile = 0;
	this->headerContent = 0;
	this->implContent = 0;
}

static void FileContent__ctor_copy(struct FileContent * this, const struct FileContent * other) {
	this->originFile = other->originFile;
	this->headerContent = other->headerContent;
	this->implContent = other->implContent;
}

static void FileOutputManagerTestFixture__ctor_default(struct FileOutputManagerTestFixture * this) {
}

static void FileOutputManagerTestFixture__ctor_copy(struct FileOutputManagerTestFixture * this, const struct FileOutputManagerTestFixture * other) {
}

bool FileOutputManagerTestFixture_fileExists(struct FileOutputManagerTestFixture * this, const int * filename) {
}

void FileOutputManagerTestFixture_TearDown(struct FileOutputManagerTestFixture * this) {
}

int TEST_F(struct FileOutputManagerTestFixture, int) {
	struct FileOutputManager manager;

}

int TEST_F_FileOutputManagerTestFixture_int(struct FileOutputManagerTestFixture, int) {
	struct FileOutputManager manager;

}

int TEST_F_FileOutputManagerTestFixture_int_1(struct FileOutputManagerTestFixture, int) {
	struct FileOutputManager manager;

}

int TEST_F_FileOutputManagerTestFixture_int_2(struct FileOutputManagerTestFixture, int) {
	struct FileOutputManager manager;

	int headerContent;

	int implContent;

	bool success;

}

int TEST_F_FileOutputManagerTestFixture_int_3(struct FileOutputManagerTestFixture, int) {
	struct FileOutputManager manager;

	int content;

	bool success;

}

