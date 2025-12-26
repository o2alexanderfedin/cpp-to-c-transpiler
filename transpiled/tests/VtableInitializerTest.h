// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/VtableInitializerTest.cpp
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
struct VtableInitializer {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void VtableInitializer__ctor_default(struct VtableInitializer * this);
static void VtableInitializer__ctor_copy(struct VtableInitializer * this, const struct VtableInitializer * other);
struct CNodeBuilder {
	int & Ctx;
};
static void CNodeBuilder__ctor_default(struct CNodeBuilder * this);
static void CNodeBuilder__ctor_copy(struct CNodeBuilder * this, const struct CNodeBuilder * other);
void CNodeBuilder__ctor(struct CNodeBuilder * this, int * Ctx);
int CNodeBuilder_intType(struct CNodeBuilder * this);
int CNodeBuilder_voidType(struct CNodeBuilder * this);
int CNodeBuilder_charType(struct CNodeBuilder * this);
int CNodeBuilder_ptrType(struct CNodeBuilder * this, int pointee);
int CNodeBuilder_structType(struct CNodeBuilder * this, int name);
int * CNodeBuilder_intVar(struct CNodeBuilder * this, int name, int initVal);
int * CNodeBuilder_intVar_int(struct CNodeBuilder * this, int name);
int * CNodeBuilder_structVar(struct CNodeBuilder * this, int type, int name);
int * CNodeBuilder_ptrVar(struct CNodeBuilder * this, int pointee, int name);
int * CNodeBuilder_var(struct CNodeBuilder * this, int type, int name, int * init);
int * CNodeBuilder_intLit(struct CNodeBuilder * this, int value);
int * CNodeBuilder_stringLit(struct CNodeBuilder * this, int str);
int * CNodeBuilder_nullPtr(struct CNodeBuilder * this);
int * CNodeBuilder_ref(struct CNodeBuilder * this, int * var);
int * CNodeBuilder_ref_int_ptr(struct CNodeBuilder * this, int * func);
int * CNodeBuilder_call(struct CNodeBuilder * this, int funcName, int args);
int * CNodeBuilder_call_int_ptr_int(struct CNodeBuilder * this, int * func, int args);
int * CNodeBuilder_member(struct CNodeBuilder * this, int * base, int field);
int * CNodeBuilder_arrowMember(struct CNodeBuilder * this, int * base, int field);
int * CNodeBuilder_assign(struct CNodeBuilder * this, int * lhs, int * rhs);
int * CNodeBuilder_addrOf(struct CNodeBuilder * this, int * expr);
int * CNodeBuilder_deref(struct CNodeBuilder * this, int * expr);
int * CNodeBuilder_block(struct CNodeBuilder * this, int stmts);
int * CNodeBuilder_returnStmt(struct CNodeBuilder * this, int * expr);
int * CNodeBuilder_declStmt(struct CNodeBuilder * this, int * decl);
int * CNodeBuilder_exprStmt(struct CNodeBuilder * this, int * expr);
int * CNodeBuilder_ifStmt(struct CNodeBuilder * this, int * cond, int * thenStmt, int * elseStmt);
int * CNodeBuilder_whileStmt(struct CNodeBuilder * this, int * cond, int * body);
int * CNodeBuilder_forStmt(struct CNodeBuilder * this, int * init, int * cond, int * inc, int * body);
int * CNodeBuilder_breakStmt(struct CNodeBuilder * this);
int * CNodeBuilder_continueStmt(struct CNodeBuilder * this);
int * CNodeBuilder_structDecl(struct CNodeBuilder * this, int name, int fields);
int * CNodeBuilder_enumDecl(struct CNodeBuilder * this, int name, int);
int * CNodeBuilder_fieldDecl(struct CNodeBuilder * this, int type, int name);
int * CNodeBuilder_forwardStructDecl(struct CNodeBuilder * this, int name);
int * CNodeBuilder_funcDecl(struct CNodeBuilder * this, int name, int retType, int params, int * body, int callConv, bool isVariadic);
int * CNodeBuilder_param(struct CNodeBuilder * this, int type, int name);
int CNodeBuilder_getCallingConvAttribute(struct CNodeBuilder * this, int CC);
int buildAST(const char * code);
int * findClass(int * TU, const int * name);
struct VtableInitializerTest {
};
static void VtableInitializerTest__ctor_default(struct VtableInitializerTest * this);
static void VtableInitializerTest__ctor_copy(struct VtableInitializerTest * this, const struct VtableInitializerTest * other);
int TEST_F(struct VtableInitializerTest, int);
int TEST_F_VtableInitializerTest_int(struct VtableInitializerTest, int);
int TEST_F_VtableInitializerTest_int_1(struct VtableInitializerTest, int);
int TEST_F_VtableInitializerTest_int_2(struct VtableInitializerTest, int);
int TEST_F_VtableInitializerTest_int_3(struct VtableInitializerTest, int);
int TEST_F_VtableInitializerTest_int_4(struct VtableInitializerTest, int);
