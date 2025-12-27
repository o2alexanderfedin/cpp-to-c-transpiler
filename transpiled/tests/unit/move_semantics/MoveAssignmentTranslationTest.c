// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/MoveAssignmentTranslationTest.cpp
// Implementation file

#include "MoveAssignmentTranslationTest.h"

static void MoveAssignmentTranslator__ctor_default(struct MoveAssignmentTranslator * this) {
	this->Context = 0;
}

static void MoveAssignmentTranslator__ctor_copy(struct MoveAssignmentTranslator * this, const struct MoveAssignmentTranslator * other) {
	this->Context = other->Context;
}

int buildAST(const char * code) {
}

static void MoveAssignmentFinder__ctor_default(struct MoveAssignmentFinder * this) {
	this->moveAssignmentOperators = 0;
}

static void MoveAssignmentFinder__ctor_copy(struct MoveAssignmentFinder * this, const struct MoveAssignmentFinder * other) {
	this->moveAssignmentOperators = other->moveAssignmentOperators;
}

bool MoveAssignmentFinder_VisitCXXMethodDecl(struct MoveAssignmentFinder * this, int * D) {
	return true;
;
}

static void MoveAssignmentTranslationTest__ctor_default(struct MoveAssignmentTranslationTest * this) {
}

static void MoveAssignmentTranslationTest__ctor_copy(struct MoveAssignmentTranslationTest * this, const struct MoveAssignmentTranslationTest * other) {
}

int TEST_F(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class Widget {\n                int* data;\n            public:\n                Widget& operator=(Widget&& other) noexcept {\n                    if (this != &other) {\n                        delete data;\n                        data = other.data;\n                        other.data = nullptr;\n                    }\n                    return *this;\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int cCode;

}

int TEST_F_MoveAssignmentTranslationTest_int(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class Container {\n                int* buffer;\n                int size;\n            public:\n                Container& operator=(Container&& other) noexcept {\n                    if (this != &other) {\n                        delete[] buffer;\n                        buffer = other.buffer;\n                        size = other.size;\n                        other.buffer = nullptr;\n                        other.size = 0;\n                    }\n                    return *this;\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int cCode;

	bool hasSelfCheck;

}

int TEST_F_MoveAssignmentTranslationTest_int_1(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class Resource {\n                int* data;\n            public:\n                ~Resource() { delete data; }\n\n                Resource& operator=(Resource&& other) noexcept {\n                    if (this != &other) {\n                        delete data;  // Clean up old resource\n                        data = other.data;\n                        other.data = nullptr;\n                    }\n                    return *this;\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int cCode;

	int destructorPos;

	int transferPos;

}

int TEST_F_MoveAssignmentTranslationTest_int_2(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class MultiResource {\n                int* buffer;\n                char* name;\n                double* values;\n            public:\n                MultiResource& operator=(MultiResource&& other) noexcept {\n                    if (this != &other) {\n                        delete[] buffer;\n                        delete[] name;\n                        delete[] values;\n\n                        buffer = other.buffer;\n                        name = other.name;\n                        values = other.values;\n\n                        other.buffer = nullptr;\n                        other.name = nullptr;\n                        other.values = nullptr;\n                    }\n                    return *this;\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int cCode;

	int nullifications = 0;

	int pos;

	int nullPattern;

}

int TEST_F_MoveAssignmentTranslationTest_int_3(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class File {\n                int fd;\n            public:\n                ~File() { /* close fd */ }\n            };\n\n            class FileManager {\n                File* file;\n                int* metadata;\n            public:\n                FileManager& operator=(FileManager&& other) noexcept {\n                    if (this != &other) {\n                        delete file;\n                        delete metadata;\n\n                        file = other.file;\n                        metadata = other.metadata;\n\n                        other.file = nullptr;\n                        other.metadata = nullptr;\n                    }\n                    return *this;\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int cCode;

}

int TEST_F_MoveAssignmentTranslationTest_int_4(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class Chain {\n                int* data;\n            public:\n                Chain& operator=(Chain&& other) noexcept {\n                    if (this != &other) {\n                        delete data;\n                        data = other.data;\n                        other.data = nullptr;\n                    }\n                    return *this;  // Return *this for chaining\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int cCode;

}

int TEST_F_MoveAssignmentTranslationTest_int_5(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class LeakPrevention {\n                int* heap_data;\n                char* heap_string;\n            public:\n                LeakPrevention& operator=(LeakPrevention&& other) noexcept {\n                    if (this != &other) {\n                        // Must clean up existing resources before assignment\n                        delete heap_data;\n                        delete[] heap_string;\n\n                        heap_data = other.heap_data;\n                        heap_string = other.heap_string;\n\n                        other.heap_data = nullptr;\n                        other.heap_string = nullptr;\n                    }\n                    return *this;\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int cCode;

}

int TEST_F_MoveAssignmentTranslationTest_int_6(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class Widget {\n                int* data;\n            public:\n                Widget& operator=(const Widget& other) {  // Copy assignment\n                    if (this != &other) {\n                        delete data;\n                        data = new int(*other.data);\n                    }\n                    return *this;\n                }\n\n                Widget& operator=(Widget&& other) noexcept {  // Move assignment\n                    if (this != &other) {\n                        delete data;\n                        data = other.data;\n                        other.data = nullptr;\n                    }\n                    return *this;\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int paramType;

}

int TEST_F_MoveAssignmentTranslationTest_int_7(struct MoveAssignmentTranslationTest, int) {
	const char *code = "\n            class MyClass {\n                int* ptr;\n            public:\n                MyClass& operator=(MyClass&& other) noexcept {\n                    if (this != &other) {\n                        delete ptr;\n                        ptr = other.ptr;\n                        other.ptr = nullptr;\n                    }\n                    return *this;\n                }\n            };\n        ";

	struct MoveAssignmentFinder finder;

	int *MoveAssign;

	struct MoveAssignmentTranslator translator;

	int cCode;

}

