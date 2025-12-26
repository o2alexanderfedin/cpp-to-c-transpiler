// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/StdMoveTranslationTest.cpp
// Implementation file

#include "StdMoveTranslationTest.h"

static void StdMoveTranslator__ctor_default(struct StdMoveTranslator * this) {
	this->Context = 0;
}

static void StdMoveTranslator__ctor_copy(struct StdMoveTranslator * this, const struct StdMoveTranslator * other) {
	this->Context = other->Context;
}

int buildAST(const char * code) {
}

static void StdMoveFinder__ctor_default(struct StdMoveFinder * this) {
	this->moveCallExprs = 0;
}

static void StdMoveFinder__ctor_copy(struct StdMoveFinder * this, const struct StdMoveFinder * other) {
	this->moveCallExprs = other->moveCallExprs;
}

bool StdMoveFinder_VisitCallExpr(struct StdMoveFinder * this, const int * Call) {
	return true;
;
}

static void StdMoveTranslationTest__ctor_default(struct StdMoveTranslationTest * this) {
}

static void StdMoveTranslationTest__ctor_copy(struct StdMoveTranslationTest * this, const struct StdMoveTranslationTest * other) {
}

int TEST_F(struct StdMoveTranslationTest, int) {
	const char *code = "\n            namespace std {\n                template<typename T>\n                T&& move(T& t) noexcept {\n                    return static_cast<T&&>(t);\n                }\n            }\n\n            class Buffer {\n                int* data;\n            public:\n                Buffer() : data(nullptr) {}\n                Buffer(Buffer&& other) : data(other.data) {\n                    other.data = nullptr;\n                }\n            };\n\n            void test() {\n                Buffer b1;\n                Buffer b2 = std::move(b1);\n            }\n        ";

	struct StdMoveFinder finder;

	const int *MoveCall;

	struct StdMoveTranslator translator;

	StdMoveTranslator::MoveContext context;

	int cCode;

}

int TEST_F_StdMoveTranslationTest_int(struct StdMoveTranslationTest, int) {
	const char *code = "\n            namespace std {\n                template<typename T>\n                T&& move(T& t) noexcept {\n                    return static_cast<T&&>(t);\n                }\n            }\n\n            class Buffer {\n                int* data;\n            public:\n                Buffer() : data(nullptr) {}\n                Buffer(Buffer&& other) : data(other.data) {\n                    other.data = nullptr;\n                }\n            };\n\n            Buffer createBuffer() {\n                Buffer local;\n                return std::move(local);\n            }\n        ";

	struct StdMoveFinder finder;

	const int *MoveCall;

	struct StdMoveTranslator translator;

	StdMoveTranslator::MoveContext context;

	int cCode;

}

int TEST_F_StdMoveTranslationTest_int_1(struct StdMoveTranslationTest, int) {
	const char *code = "\n            namespace std {\n                template<typename T>\n                T&& move(T& t) noexcept {\n                    return static_cast<T&&>(t);\n                }\n            }\n\n            class Buffer {\n                int* data;\n            public:\n                Buffer() : data(nullptr) {}\n                Buffer(Buffer&& other) : data(other.data) {\n                    other.data = nullptr;\n                }\n            };\n\n            void processBuffer(Buffer&& buf) {}\n\n            void test() {\n                Buffer obj;\n                processBuffer(std::move(obj));\n            }\n        ";

	struct StdMoveFinder finder;

	const int *MoveCall;

	struct StdMoveTranslator translator;

	StdMoveTranslator::MoveContext context;

	int cCode;

}

int TEST_F_StdMoveTranslationTest_int_2(struct StdMoveTranslationTest, int) {
	const char *code = "\n            namespace std {\n                template<typename T>\n                T&& move(T& t) noexcept {\n                    return static_cast<T&&>(t);\n                }\n            }\n\n            class MyCustomClass {\n                int value;\n            public:\n                MyCustomClass() : value(0) {}\n                MyCustomClass(MyCustomClass&& other) : value(other.value) {\n                    other.value = 0;\n                }\n            };\n\n            void test() {\n                MyCustomClass obj1;\n                MyCustomClass obj2 = std::move(obj1);\n            }\n        ";

	struct StdMoveFinder finder;

	const int *MoveCall;

	struct StdMoveTranslator translator;

	StdMoveTranslator::MoveContext context;

	int cCode;

}

int TEST_F_StdMoveTranslationTest_int_3(struct StdMoveTranslationTest, int) {
	const char *code = "\n            namespace std {\n                template<typename T>\n                T&& move(T& t) noexcept {\n                    return static_cast<T&&>(t);\n                }\n            }\n\n            namespace custom {\n                template<typename T>\n                void move(T& src, T& dest) {\n                    dest = src;\n                }\n            }\n\n            class Buffer {\n                int* data;\n            public:\n                Buffer() : data(nullptr) {}\n            };\n\n            void test() {\n                Buffer b1, b2, b3;\n                Buffer b4 = std::move(b1);  // Should detect\n                custom::move(b2, b3);       // Should NOT detect\n            }\n        ";

	struct StdMoveFinder finder;

	struct StdMoveTranslator translator;

	int stdMoveCount = 0;

}

