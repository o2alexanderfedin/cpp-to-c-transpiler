// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/comparison-operators/InequalityOperatorTest.cpp
// Implementation file

#include "InequalityOperatorTest.h"

static void InequalityOperatorTestBase__ctor_default(struct InequalityOperatorTestBase * this) {
}

static void InequalityOperatorTestBase__ctor_copy(struct InequalityOperatorTestBase * this, const struct InequalityOperatorTestBase * other) {
}

int InequalityOperatorTestBase_buildAST_const_int_ptr(struct InequalityOperatorTestBase * this, const char * code) {
}

static void InequalityOperatorTest__ctor_default(struct InequalityOperatorTest * this) {
}

static void InequalityOperatorTest__ctor_copy(struct InequalityOperatorTest * this, const struct InequalityOperatorTest * other) {
}

int TEST_F(struct InequalityOperatorTest, int) {
	const char * code = "\n        class Point {\n        public:\n            int x, y;\n            bool operator!=(const Point& other) const;\n        };\n    ";
	auto * TU;
	int * opNotEqual;
}

int TEST_F_InequalityOperatorTest_int(struct InequalityOperatorTest, int) {
	const char * code = "\n        class String {\n        public:\n            char* data;\n            bool operator!=(const String& other) const;\n        };\n    ";
	auto * TU;
	int * opNotEqual;
	int paramType;
}

int TEST_F_InequalityOperatorTest_int_1(struct InequalityOperatorTest, int) {
	const char * code = "\n        class Value {\n        public:\n            int data;\n            friend bool operator!=(const Value& a, const Value& b);\n        };\n        bool operator!=(const Value& a, const Value& b);\n    ";
	auto * TU;
	int * friendOp;
}

int TEST_F_InequalityOperatorTest_int_2(struct InequalityOperatorTest, int) {
	const char * code = "\n        class Comparable {\n        public:\n            int value;\n            bool operator==(const Comparable& other) const;\n            bool operator!=(const Comparable& other) const;\n        };\n    ";
	auto * TU;
	int * opEqual;
	int * opNotEqual;
}

int TEST_F_InequalityOperatorTest_int_3(struct InequalityOperatorTest, int) {
	const char * code = "\n        class Element {\n        public:\n            int id;\n            bool operator!=(const Element& other) const;\n        };\n    ";
	auto * TU;
	int * opNotEqual;
	int paramType;
}

int TEST_F_InequalityOperatorTest_int_4(struct InequalityOperatorTest, int) {
	const char * code = "\n        class Rectangle {\n        public:\n            int x, y, width, height;\n            bool operator!=(const Rectangle& other) const;\n        };\n    ";
	auto * TU;
	int * rectClass;
	int * opNotEqual;
	int fieldCount = 0;
}

int TEST_F_InequalityOperatorTest_int_5(struct InequalityOperatorTest, int) {
	const char * code = "\n        class Number {\n        public:\n            int value;\n            bool operator!=(const Number& other) const;\n        };\n\n        void test() {\n            Number a, b;\n            if (a != b) {\n                // Use result\n            }\n        }\n    ";
	auto * TU;
	int * testFunc;
	bool foundOperatorCall = false;
	class OperatorCallFinder {
public:
        bool found = false;
        bool VisitCXXOperatorCallExpr(int *OCE) {
                if (<recovery-expr>()) {
                        this->found = true;
                        return false;
                }
                return true;
        }
};
	OperatorCallFinder finder = ;
	foundOperatorCall = finder.found;
}

static void OperatorCallFinder__ctor_default(struct OperatorCallFinder * this) {
	this->found = 0;
}

static void OperatorCallFinder__ctor_copy(struct OperatorCallFinder * this, const struct OperatorCallFinder * other) {
	this->found = other->found;
}

bool OperatorCallFinder_VisitCXXOperatorCallExpr_int_ptr(struct OperatorCallFinder * this, int * OCE) {
	return true;
;
}

int TEST_F_InequalityOperatorTest_int_6(struct InequalityOperatorTest, int) {
	const char * code = "\n        class Wrapper {\n        public:\n            int data;\n            bool operator!=(const Wrapper& other) const;\n        };\n    ";
	auto * TU;
	int * opNotEqual;
	int returnType;
}

static void InequalityAdvancedTest__ctor_default(struct InequalityAdvancedTest * this) {
}

static void InequalityAdvancedTest__ctor_copy(struct InequalityAdvancedTest * this, const struct InequalityAdvancedTest * other) {
}

int TEST_F_InequalityAdvancedTest_int(struct InequalityAdvancedTest, int) {
	const char * code = "\n        class Multi {\n        public:\n            int value;\n            bool operator!=(const Multi& other) const;\n            bool operator!=(int other) const;\n        };\n    ";
	auto * TU;
	int opCount = 0;
}

int TEST_F_InequalityAdvancedTest_int_1(struct InequalityAdvancedTest, int) {
	const char * code = "\n        class Inline {\n        public:\n            int x;\n            bool operator!=(const Inline& other) const {\n                return x != other.x;\n            }\n        };\n    ";
	auto * TU;
	int * opNotEqual;
}

