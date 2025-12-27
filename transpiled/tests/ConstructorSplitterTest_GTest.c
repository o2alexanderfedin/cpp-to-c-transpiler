// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ConstructorSplitterTest_GTest.cpp
// Implementation file

#include "ConstructorSplitterTest_GTest.h"

static void ConstructorSplitter__ctor_default(struct ConstructorSplitter * this) {
	this->Context = 0;
	this->ViAnalyzer = 0;
}

static void ConstructorSplitter__ctor_copy(struct ConstructorSplitter * this, const struct ConstructorSplitter * other) {
	this->Context = other->Context;
	this->ViAnalyzer = other->ViAnalyzer;
}

static void VirtualMethodAnalyzer__ctor_default(struct VirtualMethodAnalyzer * this) {
	this->Context = 0;
}

static void VirtualMethodAnalyzer__ctor_copy(struct VirtualMethodAnalyzer * this, const struct VirtualMethodAnalyzer * other) {
	this->Context = other->Context;
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

static void ConstructorSplitterTestFixture__ctor_default(struct ConstructorSplitterTestFixture * this) {
}

static void ConstructorSplitterTestFixture__ctor_copy(struct ConstructorSplitterTestFixture * this, const struct ConstructorSplitterTestFixture * other) {
}

int ConstructorSplitterTestFixture_buildAST(struct ConstructorSplitterTestFixture * this, const char * code) {
}

struct CXXRecordDecl * ConstructorSplitterTestFixture_findClass(struct ConstructorSplitterTestFixture * this, int * TU, const int * name) {
	return nullptr;
;
}

int TEST_F(struct ConstructorSplitterTestFixture, int) {
	const char *code = "\n        class Base { public: virtual ~Base() {} };\n        class Derived : public virtual Base { public: int d; };\n    ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct ConstructorSplitter splitter;

	auto * TU;
	auto *Derived;

}

int TEST_F_ConstructorSplitterTestFixture_int(struct ConstructorSplitterTestFixture, int) {
	const char *code = "\n        class Base { public: virtual ~Base() {} int b; };\n        class Derived : public virtual Base {\n        public:\n            Derived() : b_data(0) {}\n            int b_data;\n        };\n    ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct ConstructorSplitter splitter;

	auto * TU;
	auto *Derived;

	int c1Code;

}

int TEST_F_ConstructorSplitterTestFixture_int_1(struct ConstructorSplitterTestFixture, int) {
	const char *code = "\n        class Base { public: virtual ~Base() {} };\n        class Derived : public virtual Base {\n        public:\n            Derived() {}\n            int d;\n        };\n    ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct ConstructorSplitter splitter;

	auto * TU;
	auto *Derived;

	int c2Code;

}

int TEST_F_ConstructorSplitterTestFixture_int_2(struct ConstructorSplitterTestFixture, int) {
	const char *code = "\n        class Base { public: virtual ~Base() {} };\n        class Left : public virtual Base { public: int l; };\n        class Right : public virtual Base { public: int r; };\n        class Diamond : public Left, public Right { public: int d; };\n    ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct ConstructorSplitter splitter;

	auto * TU;
	auto *Diamond;

	int c1Code;

}

int TEST_F_ConstructorSplitterTestFixture_int_3(struct ConstructorSplitterTestFixture, int) {
	const char *code = "\n        class Base { public: virtual ~Base() {} };\n        class Left : public virtual Base { public: int l; };\n        class Right : public virtual Base { public: int r; };\n        class Diamond : public Left, public Right { public: int d; };\n    ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct ConstructorSplitter splitter;

	auto * TU;
	auto *Diamond;

	int c1Code;

}

int TEST_F_ConstructorSplitterTestFixture_int_4(struct ConstructorSplitterTestFixture, int) {
	const char *code = "\n        class Base { public: virtual ~Base() {} };\n        class Derived : public virtual Base {\n        public:\n            Derived() {}\n        };\n    ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct ConstructorSplitter splitter;

	auto * TU;
	auto *Derived;

	int c1Code;

}

int TEST_F_ConstructorSplitterTestFixture_int_5(struct ConstructorSplitterTestFixture, int) {
	const char *code = "\n        class Base { public: virtual ~Base() {} };\n        class Derived : public Base { public: int d; };\n    ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct ConstructorSplitter splitter;

	auto * TU;
	auto *Derived;

}

int TEST_F_ConstructorSplitterTestFixture_int_6(struct ConstructorSplitterTestFixture, int) {
	const char *code = "\n        class Base { public: virtual ~Base() {} };\n        class Derived : public virtual Base {\n        public:\n            virtual void foo() {}\n        };\n    ";

	auto AST;

	struct VirtualMethodAnalyzer vmAnalyzer;

	struct VirtualInheritanceAnalyzer viAnalyzer;

	struct ConstructorSplitter splitter;

	auto * TU;
	auto *Derived;

	int c1Code;

}

