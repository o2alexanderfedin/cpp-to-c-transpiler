// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/virtual_inheritance_tests/VtableGeneratorTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct VirtualTableTestBase {
};
static void VirtualTableTestBase__ctor_default(struct VirtualTableTestBase * this);
static void VirtualTableTestBase__ctor_copy(struct VirtualTableTestBase * this, const struct VirtualTableTestBase * other);
int VirtualTableTestBase_buildAST(struct VirtualTableTestBase * this, const char * code);
int * VirtualTableTestBase_findClass(struct VirtualTableTestBase * this, int * TU, const int * name);
int VirtualTableTestBase_findAllClasses(struct VirtualTableTestBase * this, int * TU);
int * VirtualTableTestBase_findMethod(struct VirtualTableTestBase * this, int * RD, const int * methodName);
int VirtualTableTestBase_countVirtualMethods(struct VirtualTableTestBase * this, int * RD);
bool VirtualTableTestBase_isPolymorphic(struct VirtualTableTestBase * this, int * RD);
struct VirtualInheritanceTestBase {
};
static void VirtualInheritanceTestBase__ctor_default(struct VirtualInheritanceTestBase * this);
static void VirtualInheritanceTestBase__ctor_copy(struct VirtualInheritanceTestBase * this, const struct VirtualInheritanceTestBase * other);
bool VirtualInheritanceTestBase_hasVirtualBases(struct VirtualInheritanceTestBase * this, int * RD);
int VirtualInheritanceTestBase_countVirtualBases(struct VirtualInheritanceTestBase * this, int * RD);
int VirtualInheritanceTestBase_countNonVirtualBases(struct VirtualInheritanceTestBase * this, int * RD);
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
struct VtableGeneratorTest {
};
static void VtableGeneratorTest__ctor_default(struct VtableGeneratorTest * this);
static void VtableGeneratorTest__ctor_copy(struct VtableGeneratorTest * this, const struct VtableGeneratorTest * other);
int TEST_F(struct VtableGeneratorTest, int);
int TEST_F_VtableGeneratorTest_int(struct VtableGeneratorTest, int);
int TEST_F_VtableGeneratorTest_int_1(struct VtableGeneratorTest, int);
int TEST_F_VtableGeneratorTest_int_2(struct VtableGeneratorTest, int);
int TEST_F_VtableGeneratorTest_int_3(struct VtableGeneratorTest, int);
int TEST_F_VtableGeneratorTest_int_4(struct VtableGeneratorTest, int);
int TEST_F_VtableGeneratorTest_int_5(struct VtableGeneratorTest, int);
int TEST_F_VtableGeneratorTest_int_6(struct VtableGeneratorTest, int);
