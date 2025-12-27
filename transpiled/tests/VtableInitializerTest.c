// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/VtableInitializerTest.cpp
// Implementation file

#include "VtableInitializerTest.h"

static void VirtualMethodAnalyzer__ctor_default(struct VirtualMethodAnalyzer * this) {
	this->Context = 0;
}

static void VirtualMethodAnalyzer__ctor_copy(struct VirtualMethodAnalyzer * this, const struct VirtualMethodAnalyzer * other) {
	this->Context = other->Context;
}

static void VtableInitializer__ctor_default(struct VtableInitializer * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void VtableInitializer__ctor_copy(struct VtableInitializer * this, const struct VtableInitializer * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void CNodeBuilder__ctor_default(struct CNodeBuilder * this) {
	this->Ctx = 0;
}

static void CNodeBuilder__ctor_copy(struct CNodeBuilder * this, const struct CNodeBuilder * other) {
	this->Ctx = other->Ctx;
}

void CNodeBuilder__ctor(struct CNodeBuilder * this, int * Ctx) {
}

int CNodeBuilder_intType(struct CNodeBuilder * this) {
}

int CNodeBuilder_voidType(struct CNodeBuilder * this) {
}

int CNodeBuilder_charType(struct CNodeBuilder * this) {
}

int CNodeBuilder_ptrType(struct CNodeBuilder * this, int pointee) {
}

int CNodeBuilder_structType(struct CNodeBuilder * this, int name) {
	int &II;

	int *RD;

}

int * CNodeBuilder_intVar(struct CNodeBuilder * this, int name, int initVal) {
	int intTy;

	int &II;

	int *VD;

	int *IL;

}

int * CNodeBuilder_intVar_int(struct CNodeBuilder * this, int name) {
	int intTy;

	int &II;

	int *VD;

}

int * CNodeBuilder_structVar(struct CNodeBuilder * this, int type, int name) {
	int &II;

	int *VD;

}

int * CNodeBuilder_ptrVar(struct CNodeBuilder * this, int pointee, int name) {
	int ptrTy;

	int &II;

	int *VD;

}

int * CNodeBuilder_var(struct CNodeBuilder * this, int type, int name, int * init) {
	int &II;

	int *VD;

}

int * CNodeBuilder_intLit(struct CNodeBuilder * this, int value) {
}

int * CNodeBuilder_stringLit(struct CNodeBuilder * this, int str) {
}

int * CNodeBuilder_nullPtr(struct CNodeBuilder * this) {
}

int * CNodeBuilder_ref(struct CNodeBuilder * this, int * var) {
}

int * CNodeBuilder_ref_int_ptr(struct CNodeBuilder * this, int * func) {
}

int * CNodeBuilder_call(struct CNodeBuilder * this, int funcName, int args) {
	int &II;

	int DN;

	int funcType;

	int *FD;

	int *funcRef;

}

int * CNodeBuilder_call_int_ptr_int(struct CNodeBuilder * this, int * func, int args) {
	int *funcRef;

}

int * CNodeBuilder_member(struct CNodeBuilder * this, int * base, int field) {
	int baseTy;

	const int *RT;

	int *RD;

	int *FD;

}

int * CNodeBuilder_arrowMember(struct CNodeBuilder * this, int * base, int field) {
	int baseTy;

	const int *PT;

	int pointeeTy;

	const int *RT;

	int *RD;

	int *FD;

}

int * CNodeBuilder_assign(struct CNodeBuilder * this, int * lhs, int * rhs) {
}

int * CNodeBuilder_addrOf(struct CNodeBuilder * this, int * expr) {
}

int * CNodeBuilder_deref(struct CNodeBuilder * this, int * expr) {
	int exprTy;

	const int *PT;

}

int * CNodeBuilder_block(struct CNodeBuilder * this, int stmts) {
}

int * CNodeBuilder_returnStmt(struct CNodeBuilder * this, int * expr) {
}

int * CNodeBuilder_declStmt(struct CNodeBuilder * this, int * decl) {
}

int * CNodeBuilder_exprStmt(struct CNodeBuilder * this, int * expr) {
}

int * CNodeBuilder_ifStmt(struct CNodeBuilder * this, int * cond, int * thenStmt, int * elseStmt) {
}

int * CNodeBuilder_whileStmt(struct CNodeBuilder * this, int * cond, int * body) {
}

int * CNodeBuilder_forStmt(struct CNodeBuilder * this, int * init, int * cond, int * inc, int * body) {
}

int * CNodeBuilder_breakStmt(struct CNodeBuilder * this) {
}

int * CNodeBuilder_continueStmt(struct CNodeBuilder * this) {
}

int * CNodeBuilder_structDecl(struct CNodeBuilder * this, int name, int fields) {
	int &II;

	int *RD;

}

int * CNodeBuilder_enumDecl(struct CNodeBuilder * this, int name, int) {
	int &II;

	int *ED;

}

int * CNodeBuilder_fieldDecl(struct CNodeBuilder * this, int type, int name) {
	int &II;

}

int * CNodeBuilder_forwardStructDecl(struct CNodeBuilder * this, int name) {
	int &II;

}

int * CNodeBuilder_funcDecl(struct CNodeBuilder * this, int name, int retType, int params, int * body, int callConv, bool isVariadic) {
	int &II;

	int DN;

	int EPI;

	int funcType;

	int *FD;

}

int * CNodeBuilder_param(struct CNodeBuilder * this, int type, int name) {
	int &II;

}

int CNodeBuilder_getCallingConvAttribute(struct CNodeBuilder * this, int CC) {
}

int buildAST(const char * code) {
}

int * findClass(int * TU, const int * name) {
	return nullptr;
;
}

static void VtableInitializerTest__ctor_default(struct VtableInitializerTest * this) {
}

static void VtableInitializerTest__ctor_copy(struct VtableInitializerTest * this, const struct VtableInitializerTest * other) {
}

int TEST_F(struct VtableInitializerTest, int) {
	const char *code = "\n            class Shape {\n            public:\n                virtual void draw();\n                double x;  // Add a field so we have something in the struct\n            };\n        ";

	auto &Context;

	struct CNodeBuilder Builder;

	struct VirtualMethodAnalyzer analyzer;

	struct VtableInitializer initializer;

	auto * TU;
	auto *Shape;

	int thisType;

	int *thisParam;

	int *vptrInit;

}

int TEST_F_VtableInitializerTest_int(struct VtableInitializerTest, int) {
	const char *code = "\n            class Point {\n            private:\n                double x, y;\n            };\n        ";

	auto &Context;

	struct CNodeBuilder Builder;

	struct VirtualMethodAnalyzer analyzer;

	struct VtableInitializer initializer;

	auto * TU;
	auto *Point;

	int thisType;

	int *thisParam;

	int *vptrInit;

}

int TEST_F_VtableInitializerTest_int_1(struct VtableInitializerTest, int) {
	const char *code = "\n            class Shape {\n            public:\n                virtual void draw();\n            };\n        ";

	auto &Context;

	struct VirtualMethodAnalyzer analyzer;

	struct VtableInitializer initializer;

	auto * TU;
	auto *Shape;

	int vtableName;

}

int TEST_F_VtableInitializerTest_int_2(struct VtableInitializerTest, int) {
	const char *code = "\n            class Base {\n            public:\n                virtual void foo();\n            };\n\n            class Derived : public Base {\n            public:\n                void foo() override;\n            };\n        ";

	auto &Context;

	struct CNodeBuilder Builder;

	struct VirtualMethodAnalyzer analyzer;

	struct VtableInitializer initializer;

	auto * TU;
	auto *Derived;

	int thisType;

	int *thisParam;

	int *vptrInit;

	int vtableName;

}

int TEST_F_VtableInitializerTest_int_3(struct VtableInitializerTest, int) {
	const char *code = "\n            class Shape {\n            public:\n                virtual void draw();\n            };\n\n            class Animal {\n            public:\n                virtual void speak();\n            };\n        ";

	auto &Context;

	struct CNodeBuilder Builder;

	struct VirtualMethodAnalyzer analyzer;

	struct VtableInitializer initializer;

	auto * TU;
	auto *Shape;

	auto *Animal;

	int shapeVtable;

	int animalVtable;

}

int TEST_F_VtableInitializerTest_int_4(struct VtableInitializerTest, int) {
	const char *code = "\n            class Shape {\n            public:\n                virtual void draw();\n            private:\n                double x;\n            };\n        ";

	auto &Context;

	struct CNodeBuilder Builder;

	struct VirtualMethodAnalyzer analyzer;

	struct VtableInitializer initializer;

	auto * TU;
	auto *Shape;

	int thisType;

	int *thisParam;

	int *dummyExpr;

	int originalSize;

	bool injected;

}

