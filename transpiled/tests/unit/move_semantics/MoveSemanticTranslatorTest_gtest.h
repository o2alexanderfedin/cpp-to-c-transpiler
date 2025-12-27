// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/MoveSemanticTranslatorTest_gtest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct MoveSemanticTestFixture {
};
static void MoveSemanticTestFixture__ctor_default(struct MoveSemanticTestFixture * this);
static void MoveSemanticTestFixture__ctor_copy(struct MoveSemanticTestFixture * this, const struct MoveSemanticTestFixture * other);
int MoveSemanticTestFixture_buildAST(struct MoveSemanticTestFixture * this, const char * code);
struct MoveSemanticsFinder {
	int moveConstructors;
	int moveAssignments;
	int moveConstructorCalls;
	int stdMoveCalls;
	int rvalueRefs;
	int forwardingFunctions;
};
static void MoveSemanticsFinder__ctor_default(struct MoveSemanticsFinder * this);
static void MoveSemanticsFinder__ctor_copy(struct MoveSemanticsFinder * this, const struct MoveSemanticsFinder * other);
bool MoveSemanticsFinder_VisitCXXConstructorDecl(struct MoveSemanticsFinder * this, int * D);
bool MoveSemanticsFinder_VisitCXXMethodDecl(struct MoveSemanticsFinder * this, int * D);
bool MoveSemanticsFinder_VisitCXXConstructExpr(struct MoveSemanticsFinder * this, int * E);
bool MoveSemanticsFinder_VisitCallExpr(struct MoveSemanticsFinder * this, int * E);
bool MoveSemanticsFinder_VisitValueDecl(struct MoveSemanticsFinder * this, int * D);
int TEST_F(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_1(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_2(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_3(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_4(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_5(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_6(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_7(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_8(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_9(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_10(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_11(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_12(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_13(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_14(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_15(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_16(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_17(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_18(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_19(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_20(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_21(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_22(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_23(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_24(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_25(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_26(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_27(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_28(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_29(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_30(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_31(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_32(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_33(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_34(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_35(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_36(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_37(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_38(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_39(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_40(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_41(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_42(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_43(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_44(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_45(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_46(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_47(struct MoveSemanticTestFixture, int);
int TEST_F_MoveSemanticTestFixture_int_48(struct MoveSemanticTestFixture, int);
