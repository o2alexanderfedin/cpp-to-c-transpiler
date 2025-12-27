// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/VirtualBaseOffsetTableTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct VirtualMethodAnalyzer {
	int & Context;
};
static void VirtualMethodAnalyzer__ctor_default(struct VirtualMethodAnalyzer * this);
static void VirtualMethodAnalyzer__ctor_copy(struct VirtualMethodAnalyzer * this, const struct VirtualMethodAnalyzer * other);
struct VtableGenerator {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
	struct OverrideResolver * Resolver;
};
static void VtableGenerator__ctor_default(struct VtableGenerator * this);
static void VtableGenerator__ctor_copy(struct VtableGenerator * this, const struct VtableGenerator * other);
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
struct OverrideResolver {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void OverrideResolver__ctor_default(struct OverrideResolver * this);
static void OverrideResolver__ctor_copy(struct OverrideResolver * this, const struct OverrideResolver * other);
struct VtableSlot {
	int signature;
	int * method;
	unsigned int slotIndex;
};
static void VtableSlot__ctor_default(struct VtableSlot * this);
static void VtableSlot__ctor_copy(struct VtableSlot * this, const struct VtableSlot * other);
int buildAST(const char * code);
struct CXXRecordDecl * findClass(int * TU, const int * name);
struct VirtualBaseOffsetTableTest {
};
static void VirtualBaseOffsetTableTest__ctor_default(struct VirtualBaseOffsetTableTest * this);
static void VirtualBaseOffsetTableTest__ctor_copy(struct VirtualBaseOffsetTableTest * this, const struct VirtualBaseOffsetTableTest * other);
int TEST_F(struct VirtualBaseOffsetTableTest, int);
int TEST_F_VirtualBaseOffsetTableTest_int(struct VirtualBaseOffsetTableTest, int);
int TEST_F_VirtualBaseOffsetTableTest_int_1(struct VirtualBaseOffsetTableTest, int);
int TEST_F_VirtualBaseOffsetTableTest_int_2(struct VirtualBaseOffsetTableTest, int);
int TEST_F_VirtualBaseOffsetTableTest_int_3(struct VirtualBaseOffsetTableTest, int);
int TEST_F_VirtualBaseOffsetTableTest_int_4(struct VirtualBaseOffsetTableTest, int);
int TEST_F_VirtualBaseOffsetTableTest_int_5(struct VirtualBaseOffsetTableTest, int);
int TEST_F_VirtualBaseOffsetTableTest_int_6(struct VirtualBaseOffsetTableTest, int);
