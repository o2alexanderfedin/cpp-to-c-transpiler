// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/VirtualMethodIntegrationTest.cpp
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
struct VirtualCallTranslator {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void VirtualCallTranslator__ctor_default(struct VirtualCallTranslator * this);
static void VirtualCallTranslator__ctor_copy(struct VirtualCallTranslator * this, const struct VirtualCallTranslator * other);
struct VtableGenerator {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
	struct OverrideResolver * Resolver;
};
static void VtableGenerator__ctor_default(struct VtableGenerator * this);
static void VtableGenerator__ctor_copy(struct VtableGenerator * this, const struct VtableGenerator * other);
struct VirtualMethodTestBase {
};
static void VirtualMethodTestBase__ctor_default(struct VirtualMethodTestBase * this);
static void VirtualMethodTestBase__ctor_copy(struct VirtualMethodTestBase * this, const struct VirtualMethodTestBase * other);
int * VirtualMethodTestBase_parseClassDecl(struct VirtualMethodTestBase * this, const int * code, const int * className);
int * VirtualMethodTestBase_parseMemberCallExpr(struct VirtualMethodTestBase * this, const int * code);
struct CallFinder {
	int * Result;
};
static void CallFinder__ctor_default(struct CallFinder * this);
static void CallFinder__ctor_copy(struct CallFinder * this, const struct CallFinder * other);
bool CallFinder_VisitCXXMemberCallExpr(struct CallFinder * this, int * E);
int TEST_F(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_1(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_2(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_3(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_4(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_5(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_6(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_7(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_8(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_9(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_10(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_11(struct VirtualMethodTestBase, int);
int TEST_F_VirtualMethodTestBase_int_12(struct VirtualMethodTestBase, int);
struct CallFinder {
	int * Result;
};
static void CallFinder__ctor_default(struct CallFinder * this);
static void CallFinder__ctor_copy(struct CallFinder * this, const struct CallFinder * other);
bool CallFinder_VisitCXXMemberCallExpr_int_ptr(struct CallFinder * this, int * E);
int TEST_F_VirtualMethodTestBase_int_13(struct VirtualMethodTestBase, int);
int main(int argc, char * * argv);
