// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/VirtualBaseDetectionTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

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
int buildAST(const char * code);
struct CXXRecordDecl * findClass(int * TU, const int * name);
struct VirtualBaseDetectionTest {
};
static void VirtualBaseDetectionTest__ctor_default(struct VirtualBaseDetectionTest * this);
static void VirtualBaseDetectionTest__ctor_copy(struct VirtualBaseDetectionTest * this, const struct VirtualBaseDetectionTest * other);
int TEST_F(struct VirtualBaseDetectionTest, int);
int TEST_F_VirtualBaseDetectionTest_int(struct VirtualBaseDetectionTest, int);
int TEST_F_VirtualBaseDetectionTest_int_1(struct VirtualBaseDetectionTest, int);
int TEST_F_VirtualBaseDetectionTest_int_2(struct VirtualBaseDetectionTest, int);
int TEST_F_VirtualBaseDetectionTest_int_3(struct VirtualBaseDetectionTest, int);
int TEST_F_VirtualBaseDetectionTest_int_4(struct VirtualBaseDetectionTest, int);
int TEST_F_VirtualBaseDetectionTest_int_5(struct VirtualBaseDetectionTest, int);
int TEST_F_VirtualBaseDetectionTest_int_6(struct VirtualBaseDetectionTest, int);
