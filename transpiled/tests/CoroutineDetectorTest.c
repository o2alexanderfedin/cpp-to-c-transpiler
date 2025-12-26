// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/CoroutineDetectorTest.cpp
// Implementation file

#include "CoroutineDetectorTest.h"

static void LocalVariableInfo__ctor_default(struct LocalVariableInfo * this) {
	this->name = 0;
	this->type = 0;
	this->decl = 0;
}

static void LocalVariableInfo__ctor_copy(struct LocalVariableInfo * this, const struct LocalVariableInfo * other) {
	this->name = other->name;
	this->type = other->type;
	this->decl = other->decl;
}

void LocalVariableInfo__ctor(struct LocalVariableInfo * this, const int * n, const int * t, const int * d) {
}

static void CoroutineDetector__ctor_default(struct CoroutineDetector * this) {
	this->Context = 0;
}

static void CoroutineDetector__ctor_copy(struct CoroutineDetector * this, const struct CoroutineDetector * other) {
	this->Context = other->Context;
}

int buildAST(const char * code) {
}

int * findFunction(int * TU, const int * name) {
	return nullptr;
;
}

static void CoroutineDetectorTest__ctor_default(struct CoroutineDetectorTest * this) {
}

static void CoroutineDetectorTest__ctor_copy(struct CoroutineDetectorTest * this, const struct CoroutineDetectorTest * other) {
}

int TEST_F(struct CoroutineDetectorTest, int) {
	const char *code = "\n            int regular_function() {\n                return 42;\n            }\n        ";

	auto AST;

	struct CoroutineDetector detector;

	auto * TU;
	auto *func;

}

