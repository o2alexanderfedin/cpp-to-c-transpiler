// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/comparison-operators/LogicalNotOperatorTest.cpp
// Implementation file

#include "LogicalNotOperatorTest.h"

static void LogicalNotOperatorTestBase__ctor_default(struct LogicalNotOperatorTestBase * this) {
}

static void LogicalNotOperatorTestBase__ctor_copy(struct LogicalNotOperatorTestBase * this, const struct LogicalNotOperatorTestBase * other) {
}

int LogicalNotOperatorTestBase_buildAST_const_int_ptr(struct LogicalNotOperatorTestBase * this, const char * code) {
}

static void LogicalNotOperatorTest__ctor_default(struct LogicalNotOperatorTest * this) {
}

static void LogicalNotOperatorTest__ctor_copy(struct LogicalNotOperatorTest * this, const struct LogicalNotOperatorTest * other) {
}

int TEST_F(struct LogicalNotOperatorTest, int) {
	const char * code = "\n        class Boolean {\n        public:\n            bool value;\n            bool operator!() const;\n        };\n    ";
	auto * TU;
	int * opLogicalNot;
}

int TEST_F_LogicalNotOperatorTest_int(struct LogicalNotOperatorTest, int) {
	const char * code = "\n        class ConstCheckable {\n        public:\n            int value;\n            bool operator!() const;\n        };\n    ";
	auto * TU;
	int * opLogicalNot;
}

int TEST_F_LogicalNotOperatorTest_int_1(struct LogicalNotOperatorTest, int) {
	const char * code = "\n        class Unary {\n        public:\n            bool flag;\n            bool operator!() const;\n        };\n    ";
	auto * TU;
	int * opLogicalNot;
}

int TEST_F_LogicalNotOperatorTest_int_2(struct LogicalNotOperatorTest, int) {
	const char * code = "\n        class Negatable {\n        public:\n            bool state;\n            bool operator!() const;\n        };\n    ";
	auto * TU;
	int * opLogicalNot;
	int returnType;
}

int TEST_F_LogicalNotOperatorTest_int_3(struct LogicalNotOperatorTest, int) {
	const char * code = "\n        class Element {\n        public:\n            int data;\n        };\n        class SmartPtr {\n        public:\n            Element* ptr;\n            bool operator!() const;\n        };\n    ";
	auto * TU;
	int * opLogicalNot;
}

int TEST_F_LogicalNotOperatorTest_int_4(struct LogicalNotOperatorTest, int) {
	const char * code = "\n        class Checkable {\n        public:\n            int status;\n            bool operator!() const;\n        };\n        void processCheck(Checkable& obj) {\n            bool result = !obj;\n        }\n    ";
	auto * TU;
	int * opLogicalNot;
}

int TEST_F_LogicalNotOperatorTest_int_5(struct LogicalNotOperatorTest, int) {
	const char * code = "\n        class Conditional {\n        public:\n            int value;\n            bool operator!() const;\n        };\n        void ifNot(Conditional& c) {\n            if (!c) {\n                // body\n            }\n        }\n    ";
	auto * TU;
	int * opLogicalNot;
}

int TEST_F_LogicalNotOperatorTest_int_6(struct LogicalNotOperatorTest, int) {
	const char * code = "\n        class ReturnTypeCheck {\n        public:\n            unsigned int flags;\n            bool operator!() const { return false; }\n        };\n    ";
	auto * TU;
	int * opLogicalNot;
	int returnType;
}

static void LogicalNotOperatorNonConstTest__ctor_default(struct LogicalNotOperatorNonConstTest * this) {
}

static void LogicalNotOperatorNonConstTest__ctor_copy(struct LogicalNotOperatorNonConstTest * this, const struct LogicalNotOperatorNonConstTest * other) {
}

int TEST_F_LogicalNotOperatorNonConstTest_int(struct LogicalNotOperatorNonConstTest, int) {
	const char * code = "\n        class Mutable {\n        public:\n            mutable int call_count;\n            bool operator!();\n        };\n    ";
	auto * TU;
	int * opLogicalNot;
}

