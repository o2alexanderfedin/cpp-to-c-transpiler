// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/VirtualMethodIntegrationTest.cpp
// Implementation file

#include "VirtualMethodIntegrationTest.h"

static void VirtualMethodAnalyzer__ctor_default(struct VirtualMethodAnalyzer * this) {
	this->Context = 0;
}

static void VirtualMethodAnalyzer__ctor_copy(struct VirtualMethodAnalyzer * this, const struct VirtualMethodAnalyzer * other) {
	this->Context = other->Context;
}

static void OverrideResolver__ctor_default(struct OverrideResolver * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void OverrideResolver__ctor_copy(struct OverrideResolver * this, const struct OverrideResolver * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void VtableSlot__ctor_default(struct VtableSlot * this) {
	this->signature = 0;
	this->method = 0;
	this->slotIndex = 0;
}

static void VtableSlot__ctor_copy(struct VtableSlot * this, const struct VtableSlot * other) {
	this->signature = other->signature;
	this->method = other->method;
	this->slotIndex = other->slotIndex;
}

static void VirtualCallTranslator__ctor_default(struct VirtualCallTranslator * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void VirtualCallTranslator__ctor_copy(struct VirtualCallTranslator * this, const struct VirtualCallTranslator * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
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

static void VirtualMethodTestBase__ctor_default(struct VirtualMethodTestBase * this) {
}

static void VirtualMethodTestBase__ctor_copy(struct VirtualMethodTestBase * this, const struct VirtualMethodTestBase * other) {
}

int * VirtualMethodTestBase_parseClassDecl(struct VirtualMethodTestBase * this, const int * code, const int * className) {
	int &ctx;

	int *TU;

	return nullptr;
;
}

int * VirtualMethodTestBase_parseMemberCallExpr(struct VirtualMethodTestBase * this, const int * code) {
	int &ctx;

	int *TU;

	class CallFinder {
public:
        int *Result;
        bool VisitCXXMemberCallExpr(int *E) {
                return true;
        }
};

	CallFinder finder;

}

static void CallFinder__ctor_default(struct CallFinder * this) {
	this->Result = 0;
}

static void CallFinder__ctor_copy(struct CallFinder * this, const struct CallFinder * other) {
	this->Result = other->Result;
}

bool CallFinder_VisitCXXMemberCallExpr(struct CallFinder * this, int * E) {
	return true;
;
}

int TEST_F(struct VirtualMethodTestBase, int) {
	int code;

	int *record;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	auto virtualMethods;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int(struct VirtualMethodTestBase, int) {
	int code;

	int *record;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto virtualMethods;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_1(struct VirtualMethodTestBase, int) {
	int code;

	int *derivedRecord;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_2(struct VirtualMethodTestBase, int) {
	int code;

	int *derivedRecord;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_3(struct VirtualMethodTestBase, int) {
	int code;

	int *record;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto virtualMethods;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_4(struct VirtualMethodTestBase, int) {
	int code;

	int *recordC;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_5(struct VirtualMethodTestBase, int) {
	int code;

	int *recordC;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto virtualMethods;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_6(struct VirtualMethodTestBase, int) {
	int code;

	int *recordC;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto virtualMethods;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_7(struct VirtualMethodTestBase, int) {
	int code;

	int *record;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_8(struct VirtualMethodTestBase, int) {
	int code;

	int *derivedRecord;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	int vtable;

}

int TEST_F_VirtualMethodTestBase_int_9(struct VirtualMethodTestBase, int) {
	int code;

	int *record;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	auto virtualMethods;

	bool foundPureVirtual = false;

}

int TEST_F_VirtualMethodTestBase_int_10(struct VirtualMethodTestBase, int) {
	int code;

	int *abstractRecord;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	int *concreteRecord;

}

int TEST_F_VirtualMethodTestBase_int_11(struct VirtualMethodTestBase, int) {
	int code;

	int *record;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct VirtualCallTranslator translator;

	int *callExpr;

	bool isVirtual;

}

int TEST_F_VirtualMethodTestBase_int_12(struct VirtualMethodTestBase, int) {
	int code;

	int &ctx;

	int *TU;

	int *baseRecord;

	class CallFinder {
public:
        int *Result;
        bool VisitCXXMemberCallExpr(int *E) {
                return true;
        }
};

	CallFinder finder;

	struct VirtualMethodAnalyzer analyzer;

	struct VirtualCallTranslator translator;

	bool isVirtual = translator()(finder());

}

static void CallFinder__ctor_default(struct CallFinder * this) {
	this->Result = 0;
}

static void CallFinder__ctor_copy(struct CallFinder * this, const struct CallFinder * other) {
	this->Result = other->Result;
}

bool CallFinder_VisitCXXMemberCallExpr_int_ptr(struct CallFinder * this, int * E) {
	return true;
;
}

int TEST_F_VirtualMethodTestBase_int_13(struct VirtualMethodTestBase, int) {
	int code;

	int *derivedRecord;

	int &ctx;

	struct VirtualMethodAnalyzer analyzer;

	struct OverrideResolver resolver;

	struct VtableGenerator generator;

	auto virtualMethods;

	bool hasClone = false;

}

int main(int argc, char * * argv) {
}

