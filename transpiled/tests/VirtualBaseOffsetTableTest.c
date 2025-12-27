// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/VirtualBaseOffsetTableTest.cpp
// Implementation file

#include "VirtualBaseOffsetTableTest.h"

static void VirtualMethodAnalyzer__ctor_default(struct VirtualMethodAnalyzer * this) {
	this->Context = 0;
}

static void VirtualMethodAnalyzer__ctor_copy(struct VirtualMethodAnalyzer * this, const struct VirtualMethodAnalyzer * other) {
	this->Context = other->Context;
}

static void VtableGenerator__ctor_default(struct VtableGenerator * this) {
	this->Context = 0;
	this->Analyzer = 0;
	this->Resolver = 0;
}

static void VtableGenerator__ctor_copy(struct VtableGenerator * this, const struct VtableGenerator * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
	this->Resolver = other->Resolver;
}

static void BaseClassInfo__ctor_default(struct BaseClassInfo * this) {
	this->baseClass = 0;
	this->isVirtual = 0;
	this->accessSpecifier = 0;
}

static void BaseClassInfo__ctor_copy(struct BaseClassInfo * this, const struct BaseClassInfo * other) {
	this->baseClass = other->baseClass;
	this->isVirtual = other->isVirtual;
	this->accessSpecifier = other->accessSpecifier;
}

void BaseClassInfo__ctor(struct BaseClassInfo * this, const struct CXXRecordDecl * base, bool virt, int access) {
	this->baseClass = base;
	this->isVirtual = virt;
}

static void InheritanceGraph__ctor_default(struct InheritanceGraph * this) {
}

static void InheritanceGraph__ctor_copy(struct InheritanceGraph * this, const struct InheritanceGraph * other) {
}

static void VirtualInheritanceAnalyzer__ctor_default(struct VirtualInheritanceAnalyzer * this) {
	InheritanceGraph__ctor_default(&this->inheritanceGraph);
	this->needsVTTSet = 0;
	this->diamondPatterns = 0;
}

static void VirtualInheritanceAnalyzer__ctor_copy(struct VirtualInheritanceAnalyzer * this, const struct VirtualInheritanceAnalyzer * other) {
	InheritanceGraph__ctor_copy(&this->inheritanceGraph, &other->inheritanceGraph);
	this->needsVTTSet = other->needsVTTSet;
	this->diamondPatterns = other->diamondPatterns;
}

const struct InheritanceGraph * VirtualInheritanceAnalyzer_getInheritanceGraph(struct VirtualInheritanceAnalyzer * this) {
	return this->inheritanceGraph;
;
}

static void OverrideResolver__ctor_default(struct OverrideResolver * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void OverrideResolver__ctor_copy(struct OverrideResolver * this, const struct OverrideResolver * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void VtableSlot__ctor_default(struct VtableSlot * this) {
	this->signature = 0;
	this->method = 0;
	this->slotIndex = 0;
}

static void VtableSlot__ctor_copy(struct VtableSlot * this, const struct VtableSlot * other) {
	this->signature = other->signature;
	this->method = other->method;
	this->slotIndex = other->slotIndex;
}

int buildAST(const char * code) {
}

struct CXXRecordDecl * findClass(int * TU, const int * name) {
	return nullptr;
;
}

static void VirtualBaseOffsetTableTest__ctor_default(struct VirtualBaseOffsetTableTest * this) {
}

static void VirtualBaseOffsetTableTest__ctor_copy(struct VirtualBaseOffsetTableTest * this, const struct VirtualBaseOffsetTableTest * other) {
}

int TEST_F(struct VirtualBaseOffsetTableTest, int) {
	const char *code = "\n            class Base {\n            public:\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Derived : public virtual Base {\n            public:\n                int d;\n            };\n        ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto * TU;
	auto *Base;

	auto *Derived;

	int vtableCode;

}

int TEST_F_VirtualBaseOffsetTableTest_int(struct VirtualBaseOffsetTableTest, int) {
	const char *code = "\n            class Base {\n            public:\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Left : public virtual Base {\n            public:\n                int l;\n            };\n\n            class Right : public virtual Base {\n            public:\n                int r;\n            };\n\n            class Diamond : public Left, public Right {\n            public:\n                int d;\n            };\n        ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto * TU;
	auto *Base;

	auto *Left;

	auto *Right;

	auto *Diamond;

	int vtableCode;

}

int TEST_F_VirtualBaseOffsetTableTest_int_1(struct VirtualBaseOffsetTableTest, int) {
	const char *code = "\n            class Base1 {\n            public:\n                virtual ~Base1() {}\n                int b1;\n            };\n\n            class Base2 {\n            public:\n                virtual ~Base2() {}\n                int b2;\n            };\n\n            class Derived : public virtual Base1, public virtual Base2 {\n            public:\n                int d;\n            };\n        ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto * TU;
	auto *Base1;

	auto *Base2;

	auto *Derived;

	int vtableCode;

	int count;

	int pos;

}

int TEST_F_VirtualBaseOffsetTableTest_int_2(struct VirtualBaseOffsetTableTest, int) {
	const char *code = "\n            class Base {\n            public:\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Derived : public virtual Base {\n            public:\n                int d1;\n                int d2;\n            };\n        ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto * TU;
	auto *Derived;

	int offset;

}

int TEST_F_VirtualBaseOffsetTableTest_int_3(struct VirtualBaseOffsetTableTest, int) {
	const char *code = "\n            class Base {\n            public:\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Derived : public virtual Base {\n            public:\n                virtual void foo() {}\n                int d;\n            };\n        ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto * TU;
	auto *Derived;

	int vtableCode;

	int offsetPos;

	int funcPtrPos;

}

int TEST_F_VirtualBaseOffsetTableTest_int_4(struct VirtualBaseOffsetTableTest, int) {
	const char *code = "\n            class Base {\n            public:\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Derived : public virtual Base {\n            public:\n                int d;\n            };\n        ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto * TU;
	auto *Base;

	auto *Derived;

	int helperCode;

}

int TEST_F_VirtualBaseOffsetTableTest_int_5(struct VirtualBaseOffsetTableTest, int) {
	const char *code = "\n            class Base {\n            public:\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Derived : public Base {  // NOT virtual\n            public:\n                int d;\n            };\n        ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto * TU;
	auto *Derived;

	int vtableCode;

}

int TEST_F_VirtualBaseOffsetTableTest_int_6(struct VirtualBaseOffsetTableTest, int) {
	const char *code = "\n            class Base {\n            public:\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Middle : public virtual Base {\n            public:\n                int m;\n            };\n\n            class Derived : public Middle {\n            public:\n                int d;\n            };\n        ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto * TU;
	auto *Base;

	auto *Middle;

	auto *Derived;

	int vtableCode;

}

