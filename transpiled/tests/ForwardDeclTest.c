// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ForwardDeclTest.cpp
// Implementation file

#include "ForwardDeclTest.h"

static void HeaderSeparator__ctor_default(struct HeaderSeparator * this) {
	this->headerDecls = 0;
	this->implDecls = 0;
	this->forwardDecls = 0;
}

static void HeaderSeparator__ctor_copy(struct HeaderSeparator * this, const struct HeaderSeparator * other) {
	this->headerDecls = other->headerDecls;
	this->implDecls = other->implDecls;
	this->forwardDecls = other->forwardDecls;
}

const int * HeaderSeparator_getHeaderDecls(struct HeaderSeparator * this) {
}

const int * HeaderSeparator_getImplDecls(struct HeaderSeparator * this) {
}

const int * HeaderSeparator_getForwardDecls(struct HeaderSeparator * this) {
}

int TEST(int, int) {
	const char *Code = "\n            struct Node {\n                int data;\n                struct Node *next;  // Pointer to incomplete type\n            };\n        ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	auto forwardDecls = separator()();

}

int TEST_int_int(int, int) {
	const char *Code = "\n            struct B;  // Forward declaration already in source (but we detect it anyway)\n\n            struct A {\n                struct B *bPtr;\n            };\n\n            struct B {\n                struct A *aPtr;\n            };\n        ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	auto forwardDecls = separator()();

}

int TEST_int_int_1(int, int) {
	const char *Code = "\n            struct Node {\n                int data;\n                struct Node *next;\n                struct Node *prev;\n                struct Node *parent;\n            };\n        ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	auto forwardDecls = separator()();

}

int TEST_int_int_2(int, int) {
	const char *Code = "\n            struct Point {\n                int x;\n                int y;\n            };\n\n            struct Rectangle {\n                struct Point topLeft;    // Embedded struct (not pointer)\n                struct Point bottomRight;\n            };\n        ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	auto forwardDecls = separator()();

}

int TEST_int_int_3(int, int) {
	const char *Code = "\n            struct Container {\n                int *intPtr;\n                double *doublePtr;\n                char *charPtr;\n            };\n        ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	auto forwardDecls = separator()();

}

int TEST_int_int_4(int, int) {
	const char *Code = "\n            struct Tree {\n                int value;\n                struct Node *root;\n            };\n\n            struct Node {\n                int data;\n                struct Tree *owner;\n                struct Node *left;\n                struct Node *right;\n            };\n\n            struct Forest {\n                struct Tree *trees;\n                int count;\n            };\n        ";

	auto AST;

	auto * TU;
	struct HeaderSeparator separator;

	auto forwardDecls = separator()();

}

