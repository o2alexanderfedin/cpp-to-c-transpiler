// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/VirtualBaseDetectionTest.cpp
// Implementation file

#include "VirtualBaseDetectionTest.h"

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

int buildAST(const char * code) {
}

struct CXXRecordDecl * findClass(int * TU, const int * name) {
	return nullptr;
;
}

static void VirtualBaseDetectionTest__ctor_default(struct VirtualBaseDetectionTest * this) {
}

static void VirtualBaseDetectionTest__ctor_copy(struct VirtualBaseDetectionTest * this, const struct VirtualBaseDetectionTest * other) {
}

int TEST_F(struct VirtualBaseDetectionTest, int) {
	const char *code = "\n            class Base {\n                virtual ~Base() {}\n                int x;\n            };\n\n            class Derived : public virtual Base {\n                int y;\n            };\n        ";

	auto AST;

	auto * TU;
	auto *Base;

	auto *Derived;

	struct VirtualInheritanceAnalyzer analyzer;

	auto vbases;

}

int TEST_F_VirtualBaseDetectionTest_int(struct VirtualBaseDetectionTest, int) {
	const char *code = "\n            class Base {\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Left : public virtual Base {\n                int l;\n            };\n\n            class Right : public virtual Base {\n                int r;\n            };\n\n            class Diamond : public Left, public Right {\n                int d;\n            };\n        ";

	auto AST;

	auto * TU;
	auto *Base;

	auto *Left;

	auto *Right;

	auto *Diamond;

	struct VirtualInheritanceAnalyzer analyzer;

	auto vbases;

}

int TEST_F_VirtualBaseDetectionTest_int_1(struct VirtualBaseDetectionTest, int) {
	const char *code = "\n            class Base {\n                virtual ~Base() {}\n                int x;\n            };\n\n            class Derived : public Base {  // NOT virtual\n                int y;\n            };\n        ";

	auto AST;

	auto * TU;
	auto *Base;

	auto *Derived;

	struct VirtualInheritanceAnalyzer analyzer;

}

int TEST_F_VirtualBaseDetectionTest_int_2(struct VirtualBaseDetectionTest, int) {
	const char *code = "\n            class Base {\n                virtual ~Base() {}\n                int b;\n            };\n\n            class Left : public virtual Base {\n                int l;\n            };\n\n            class Right : public virtual Base {\n                int r;\n            };\n\n            class Diamond : public Left, public Right {\n                int d;\n            };\n        ";

	auto AST;

	auto * TU;
	auto *Base;

	auto *Left;

	auto *Right;

	auto *Diamond;

	struct VirtualInheritanceAnalyzer analyzer;

	const InheritanceGraph &graph = VirtualInheritanceAnalyzer_getInheritanceGraph(&analyzer);

	auto leftParents;

	auto rightParents;

	auto diamondParents;

	auto paths;

}

int TEST_F_VirtualBaseDetectionTest_int_3(struct VirtualBaseDetectionTest, int) {
	const char *code = "\n            class Base {\n                virtual ~Base() {}\n            };\n\n            class Derived : public virtual Base {\n            };\n\n            class MostDerived : public Derived {\n            };\n        ";

	auto AST;

	auto * TU;
	auto *Base;

	auto *Derived;

	auto *MostDerived;

	struct VirtualInheritanceAnalyzer analyzer;

}

int TEST_F_VirtualBaseDetectionTest_int_4(struct VirtualBaseDetectionTest, int) {
	const char *code = "\n            class Base1 {\n                virtual ~Base1() {}\n                int b1;\n            };\n\n            class Base2 {\n                virtual ~Base2() {}\n                int b2;\n            };\n\n            class Derived : public virtual Base1, public virtual Base2 {\n                int d;\n            };\n        ";

	auto AST;

	auto * TU;
	auto *Base1;

	auto *Base2;

	auto *Derived;

	struct VirtualInheritanceAnalyzer analyzer;

	auto vbases;

}

int TEST_F_VirtualBaseDetectionTest_int_5(struct VirtualBaseDetectionTest, int) {
	const char *code = "\n            class Base {\n                virtual ~Base() {}\n            };\n\n            class Middle : public virtual Base {\n            };\n\n            class Derived : public Middle {\n            };\n        ";

	auto AST;

	auto * TU;
	auto *Base;

	auto *Middle;

	auto *Derived;

	struct VirtualInheritanceAnalyzer analyzer;

	auto vbases;

}

int TEST_F_VirtualBaseDetectionTest_int_6(struct VirtualBaseDetectionTest, int) {
	const char *code = "\n            class VirtualBase {\n                virtual ~VirtualBase() {}\n                int vb;\n            };\n\n            class NonVirtualBase {\n                virtual ~NonVirtualBase() {}\n                int nvb;\n            };\n\n            class Derived : public virtual VirtualBase, public NonVirtualBase {\n                int d;\n            };\n        ";

	auto AST;

	auto * TU;
	auto *VirtualBase;

	auto *NonVirtualBase;

	auto *Derived;

	struct VirtualInheritanceAnalyzer analyzer;

	auto vbases;

	const InheritanceGraph &graph = VirtualInheritanceAnalyzer_getInheritanceGraph(&analyzer);

	auto parents;

	bool foundVirtual = false;

	bool foundNonVirtual = false;

}

