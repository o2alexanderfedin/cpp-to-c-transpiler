// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ValidationTest.cpp
// Implementation file

#include "ValidationTest.h"

static void CodeGenerator__ctor_default(struct CodeGenerator * this) {
	this->OS = 0;
	this->Policy = 0;
	this->Context = 0;
	this->CurrentInputFile = 0;
}

static void CodeGenerator__ctor_copy(struct CodeGenerator * this, const struct CodeGenerator * other) {
	this->OS = other->OS;
	this->Policy = other->Policy;
	this->Context = other->Context;
	this->CurrentInputFile = other->CurrentInputFile;
}

static void CNodeBuilder__ctor_default(struct CNodeBuilder * this) {
	this->Ctx = 0;
}

static void CNodeBuilder__ctor_copy(struct CNodeBuilder * this, const struct CNodeBuilder * other) {
	this->Ctx = other->Ctx;
}

void CNodeBuilder__ctor_1(struct CNodeBuilder * this, int * Ctx) {
}

