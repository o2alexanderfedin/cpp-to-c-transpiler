// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/IntegrationTest.cpp
// Implementation file

#include "IntegrationTest.h"

static void HeaderSeparator__ctor_default(struct HeaderSeparator * this) {
	this->headerDecls = 0;
	this->implDecls = 0;
	this->forwardDecls = 0;
}

static void HeaderSeparator__ctor_copy(struct HeaderSeparator * this, const struct HeaderSeparator * other) {
	this->headerDecls = other->headerDecls;
	this->implDecls = other->implDecls;
	this->forwardDecls = other->forwardDecls;
}

const int * HeaderSeparator_getHeaderDecls(struct HeaderSeparator * this) {
}

const int * HeaderSeparator_getImplDecls(struct HeaderSeparator * this) {
}

const int * HeaderSeparator_getForwardDecls(struct HeaderSeparator * this) {
}

static void IncludeGuardGenerator__ctor_copy(struct IncludeGuardGenerator * this, const struct IncludeGuardGenerator * other) {
	this->m_usePragmaOnce = other->m_usePragmaOnce;
}

static void DependencyAnalyzer__ctor_default(struct DependencyAnalyzer * this) {
	this->ownHeader = 0;
	this->runtimeDeps = 0;
}

static void DependencyAnalyzer__ctor_copy(struct DependencyAnalyzer * this, const struct DependencyAnalyzer * other) {
	this->ownHeader = other->ownHeader;
	this->runtimeDeps = other->runtimeDeps;
}

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

int TEST(int, int) {
	const char *Code = "\n        struct Point {\n            int x, y;\n        };\n\n        void printPoint(struct Point *p);\n    ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	struct IncludeGuardGenerator guardGen;

	int guardName;

	int guardBegin;

	int guardEnd;

}

int TEST_int_int(int, int) {
	const char *Code = "\n        struct Node {\n            int data;\n            struct Node *next;\n        };\n    ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	auto forwardDecls = separator()();

}

int TEST_int_int_1(int, int) {
	struct DependencyAnalyzer depAnalyzer;

	struct IncludeGuardGenerator guardGen;

	int guardName;

	int includes;

}

int TEST_int_int_2(int, int) {
	struct FileOutputManager fileManager;

	struct IncludeGuardGenerator guardGen;

	int guardName;

	int guardBegin;

	int guardEnd;

	struct DependencyAnalyzer depAnalyzer;

	int includes;

	int headerContent;

	int implContent;

	bool success;

}

int TEST_int_int_3(int, int) {
	const char *Code = "\n        struct Calculator {\n            int add(int a, int b);\n            int subtract(int a, int b);\n        };\n\n        int Calculator::add(int a, int b) { return a + b; }\n        int Calculator::subtract(int a, int b) { return a - b; }\n    ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	struct IncludeGuardGenerator guardGen;

	int guardName;

	int guardBegin;

	int guardEnd;

	struct DependencyAnalyzer depAnalyzer;

	struct FileOutputManager fileManager;

}

