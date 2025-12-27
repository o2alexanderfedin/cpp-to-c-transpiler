// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/virtual_inheritance_tests/VtableGeneratorTest.cpp
// Implementation file

#include "VtableGeneratorTest.h"

static void VirtualTableTestBase__ctor_default(struct VirtualTableTestBase * this) {
}

static void VirtualTableTestBase__ctor_copy(struct VirtualTableTestBase * this, const struct VirtualTableTestBase * other) {
}

int VirtualTableTestBase_buildAST(struct VirtualTableTestBase * this, const char * code) {
}

int * VirtualTableTestBase_findClass(struct VirtualTableTestBase * this, int * TU, const int * name) {
	return nullptr;
;
}

int VirtualTableTestBase_findAllClasses(struct VirtualTableTestBase * this, int * TU) {
}

int * VirtualTableTestBase_findMethod(struct VirtualTableTestBase * this, int * RD, const int * methodName) {
	return nullptr;
;
}

int VirtualTableTestBase_countVirtualMethods(struct VirtualTableTestBase * this, int * RD) {
	int count;

}

bool VirtualTableTestBase_isPolymorphic(struct VirtualTableTestBase * this, int * RD) {
}

static void VirtualInheritanceTestBase__ctor_default(struct VirtualInheritanceTestBase * this) {
}

static void VirtualInheritanceTestBase__ctor_copy(struct VirtualInheritanceTestBase * this, const struct VirtualInheritanceTestBase * other) {
}

bool VirtualInheritanceTestBase_hasVirtualBases(struct VirtualInheritanceTestBase * this, int * RD) {
}

int VirtualInheritanceTestBase_countVirtualBases(struct VirtualInheritanceTestBase * this, int * RD) {
}

int VirtualInheritanceTestBase_countNonVirtualBases(struct VirtualInheritanceTestBase * this, int * RD) {
}

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

static void VtableGeneratorTest__ctor_default(struct VtableGeneratorTest * this) {
}

static void VtableGeneratorTest__ctor_copy(struct VtableGeneratorTest * this, const struct VtableGeneratorTest * other) {
}

int TEST_F(struct VtableGeneratorTest, int) {
	const char *code = "\n        class Base {\n        public:\n            virtual ~Base() {}\n            virtual void foo() {}\n        };\n    ";

	struct VirtualMethodAnalyzer analyzer;

	struct VtableGenerator generator;

	auto *TU;

	auto *Base;

	int vtableCode;

}

int TEST_F_VtableGeneratorTest_int(struct VtableGeneratorTest, int) {
	const char *code = "\n        class Shape {\n        public:\n            virtual ~Shape() {}\n            virtual double area() { return 0.0; }\n            virtual void draw() {}\n        };\n    ";

	struct VirtualMethodAnalyzer analyzer;

	struct VtableGenerator generator;

	auto *TU;

	auto *Shape;

	auto methods;

}

int TEST_F_VtableGeneratorTest_int_1(struct VtableGeneratorTest, int) {
	const char *code = "\n        class Widget {\n        public:\n            virtual ~Widget() {}\n            virtual void render() {}\n            virtual void update() {}\n            virtual bool validate() { return true; }\n        };\n    ";

	struct VirtualMethodAnalyzer analyzer;

	struct VtableGenerator generator;

	auto *TU;

	auto *Widget;

	int vtableCode;

}

int TEST_F_VtableGeneratorTest_int_2(struct VtableGeneratorTest, int) {
	const char *code = "\n        class Base {\n        public:\n            virtual ~Base() {}\n            virtual void foo() {}\n        };\n\n        class Derived : public Base {\n        public:\n            void foo() override {}\n            virtual void bar() {}\n        };\n    ";

	struct VirtualMethodAnalyzer analyzer;

	struct VtableGenerator generator;

	auto *TU;

	auto *Derived;

	int vtableCode;

}

int TEST_F_VtableGeneratorTest_int_3(struct VtableGeneratorTest, int) {
	const char *code = "\n        class Calculator {\n        public:\n            virtual ~Calculator() {}\n            virtual int add(int a, int b) { return a + b; }\n            virtual double multiply(double x, double y) { return x * y; }\n        };\n    ";

	struct VirtualMethodAnalyzer analyzer;

	struct VtableGenerator generator;

	auto *TU;

	auto *Calculator;

	int vtableCode;

}

int TEST_F_VtableGeneratorTest_int_4(struct VtableGeneratorTest, int) {
	const char *code = "\n        class Regular {\n        public:\n            void foo() {}\n            int bar() { return 42; }\n        };\n    ";

	struct VirtualMethodAnalyzer analyzer;

	struct VtableGenerator generator;

	auto *TU;

	auto *Regular;

	int vtableCode;

}

int TEST_F_VtableGeneratorTest_int_5(struct VtableGeneratorTest, int) {
	const char *code = "\n        class Abstract {\n        public:\n            virtual ~Abstract() {}\n            virtual void foo() = 0;\n            virtual int bar() = 0;\n        };\n    ";

	struct VirtualMethodAnalyzer analyzer;

	struct VtableGenerator generator;

	auto *TU;

	auto *Abstract;

	int vtableCode;

}

int TEST_F_VtableGeneratorTest_int_6(struct VtableGeneratorTest, int) {
	const char *code = "\n        class Base {\n        public:\n            virtual ~Base() {}\n            virtual void foo() {}\n        };\n\n        class Middle : public Base {\n        public:\n            void foo() override {}\n            virtual void bar() {}\n        };\n\n        class Derived : public Middle {\n        public:\n            void bar() override {}\n            virtual void baz() {}\n        };\n    ";

	struct VirtualMethodAnalyzer analyzer;

	struct VtableGenerator generator;

	auto *TU;

	auto *Derived;

	int vtableCode;

}

