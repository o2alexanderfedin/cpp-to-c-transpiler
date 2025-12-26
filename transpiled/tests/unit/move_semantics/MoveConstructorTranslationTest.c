// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/MoveConstructorTranslationTest.cpp
// Implementation file

#include "MoveConstructorTranslationTest.h"

static void MoveConstructorTranslator__ctor_default(struct MoveConstructorTranslator * this) {
	this->Context = 0;
}

static void MoveConstructorTranslator__ctor_copy(struct MoveConstructorTranslator * this, const struct MoveConstructorTranslator * other) {
	this->Context = other->Context;
}

int buildAST(const char * code) {
}

static void MoveConstructorFinder__ctor_default(struct MoveConstructorFinder * this) {
	this->moveConstructors = 0;
}

static void MoveConstructorFinder__ctor_copy(struct MoveConstructorFinder * this, const struct MoveConstructorFinder * other) {
	this->moveConstructors = other->moveConstructors;
}

bool MoveConstructorFinder_VisitCXXConstructorDecl(struct MoveConstructorFinder * this, int * D) {
	return true;
;
}

static void MoveConstructorTranslationTest__ctor_default(struct MoveConstructorTranslationTest * this) {
}

static void MoveConstructorTranslationTest__ctor_copy(struct MoveConstructorTranslationTest * this, const struct MoveConstructorTranslationTest * other) {
}

int TEST_F(struct MoveConstructorTranslationTest, int) {
	const char *code = "\n            class Widget {\n                int* data;\n            public:\n                Widget(Widget&& other) : data(other.data) {\n                    other.data = nullptr;\n                }\n            };\n        ";

	struct MoveConstructorFinder finder;

	int *MoveCtor;

	struct MoveConstructorTranslator translator;

	int cCode;

}

int TEST_F_MoveConstructorTranslationTest_int(struct MoveConstructorTranslationTest, int) {
	const char *code = "\n            class Resource {\n                int* buffer;\n                char* name;\n                double* metrics;\n            public:\n                Resource(Resource&& other)\n                    : buffer(other.buffer), name(other.name), metrics(other.metrics) {\n                    other.buffer = nullptr;\n                    other.name = nullptr;\n                    other.metrics = nullptr;\n                }\n            };\n        ";

	struct MoveConstructorFinder finder;

	int *MoveCtor;

	struct MoveConstructorTranslator translator;

	int cCode;

	int nullifications = 0;

	int pos;

}

int TEST_F_MoveConstructorTranslationTest_int_1(struct MoveConstructorTranslationTest, int) {
	const char *code = "\n            class Data {\n                int* ptr;\n                int size;\n                bool valid;\n            public:\n                Data(Data&& other)\n                    : ptr(other.ptr), size(other.size), valid(other.valid) {\n                    other.ptr = nullptr;\n                    other.size = 0;\n                    other.valid = false;\n                }\n            };\n        ";

	struct MoveConstructorFinder finder;

	int *MoveCtor;

	struct MoveConstructorTranslator translator;

	int cCode;

}

int TEST_F_MoveConstructorTranslationTest_int_2(struct MoveConstructorTranslationTest, int) {
	const char *code = "\n            class Container {\n                int* data;\n                int capacity;\n            public:\n                Container(Container&& other) noexcept\n                    : data(other.data), capacity(other.capacity) {\n                    other.data = nullptr;\n                    other.capacity = 0;\n                }\n            };\n        ";

	struct MoveConstructorFinder finder;

	int *MoveCtor;

	struct MoveConstructorTranslator translator;

	int cCode;

}

int TEST_F_MoveConstructorTranslationTest_int_3(struct MoveConstructorTranslationTest, int) {
	const char *code = "\n            class Widget {\n                int* data;\n            public:\n                Widget() : data(new int(0)) {}\n                Widget(const Widget& other) : data(new int(*other.data)) {}\n                Widget(Widget&& other) : data(other.data) {\n                    other.data = nullptr;\n                }\n            };\n        ";

	struct MoveConstructorFinder finder;

	int *MoveCtor;

	struct MoveConstructorTranslator translator;

	int cCode;

}

int TEST_F_MoveConstructorTranslationTest_int_4(struct MoveConstructorTranslationTest, int) {
	const char *code = "\n            class Widget {\n                int* data;\n            public:\n                Widget(const Widget& other) : data(new int(*other.data)) {}  // Copy\n                Widget(Widget&& other) : data(other.data) {                  // Move\n                    other.data = nullptr;\n                }\n            };\n        ";

	struct MoveConstructorFinder finder;

	int *MoveCtor;

	struct MoveConstructorTranslator translator;

	int paramType;

}

int TEST_F_MoveConstructorTranslationTest_int_5(struct MoveConstructorTranslationTest, int) {
	const char *code = "\n            class MyClass {\n                int* ptr;\n            public:\n                MyClass(MyClass&& other) noexcept : ptr(other.ptr) {\n                    other.ptr = nullptr;\n                }\n            };\n        ";

	struct MoveConstructorFinder finder;

	int *MoveCtor;

	struct MoveConstructorTranslator translator;

	int cCode;

}

