// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ConstructorSplitterTest_GTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct ConstructorSplitter {
	int & Context;
	const VirtualInheritanceAnalyzer & ViAnalyzer;
};
static void ConstructorSplitter__ctor_default(struct ConstructorSplitter * this);
static void ConstructorSplitter__ctor_copy(struct ConstructorSplitter * this, const struct ConstructorSplitter * other);
struct VirtualMethodAnalyzer {
	int & Context;
};
static void VirtualMethodAnalyzer__ctor_default(struct VirtualMethodAnalyzer * this);
static void VirtualMethodAnalyzer__ctor_copy(struct VirtualMethodAnalyzer * this, const struct VirtualMethodAnalyzer * other);
struct BaseClassInfo {
	const struct CXXRecordDecl * baseClass;
	bool isVirtual;
	int accessSpecifier;
};
static void BaseClassInfo__ctor_default(struct BaseClassInfo * this);
static void BaseClassInfo__ctor_copy(struct BaseClassInfo * this, const struct BaseClassInfo * other);
void BaseClassInfo__ctor(struct BaseClassInfo * this, const struct CXXRecordDecl * base, bool virt, int access);
struct InheritanceGraph {
};
static void InheritanceGraph__ctor_default(struct InheritanceGraph * this);
static void InheritanceGraph__ctor_copy(struct InheritanceGraph * this, const struct InheritanceGraph * other);
struct VirtualInheritanceAnalyzer {
	struct InheritanceGraph inheritanceGraph;
	int needsVTTSet;
	int diamondPatterns;
};
static void VirtualInheritanceAnalyzer__ctor_default(struct VirtualInheritanceAnalyzer * this);
static void VirtualInheritanceAnalyzer__ctor_copy(struct VirtualInheritanceAnalyzer * this, const struct VirtualInheritanceAnalyzer * other);
const struct InheritanceGraph * VirtualInheritanceAnalyzer_getInheritanceGraph(struct VirtualInheritanceAnalyzer * this);
struct ConstructorSplitterTestFixture {
};
static void ConstructorSplitterTestFixture__ctor_default(struct ConstructorSplitterTestFixture * this);
static void ConstructorSplitterTestFixture__ctor_copy(struct ConstructorSplitterTestFixture * this, const struct ConstructorSplitterTestFixture * other);
int ConstructorSplitterTestFixture_buildAST(struct ConstructorSplitterTestFixture * this, const char * code);
struct CXXRecordDecl * ConstructorSplitterTestFixture_findClass(struct ConstructorSplitterTestFixture * this, int * TU, const int * name);
int TEST_F(struct ConstructorSplitterTestFixture, int);
int TEST_F_ConstructorSplitterTestFixture_int(struct ConstructorSplitterTestFixture, int);
int TEST_F_ConstructorSplitterTestFixture_int_1(struct ConstructorSplitterTestFixture, int);
int TEST_F_ConstructorSplitterTestFixture_int_2(struct ConstructorSplitterTestFixture, int);
int TEST_F_ConstructorSplitterTestFixture_int_3(struct ConstructorSplitterTestFixture, int);
int TEST_F_ConstructorSplitterTestFixture_int_4(struct ConstructorSplitterTestFixture, int);
int TEST_F_ConstructorSplitterTestFixture_int_5(struct ConstructorSplitterTestFixture, int);
int TEST_F_ConstructorSplitterTestFixture_int_6(struct ConstructorSplitterTestFixture, int);
