// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ComStyleAllMethodsTest.cpp
// Implementation file

#include "ComStyleAllMethodsTest.h"

static void ComStyleAllMethodsTest__ctor_default(struct ComStyleAllMethodsTest * this) {
	this->AST = 0;
}

static void ComStyleAllMethodsTest__ctor_copy(struct ComStyleAllMethodsTest * this, const struct ComStyleAllMethodsTest * other) {
	this->AST = other->AST;
}

int ComStyleAllMethodsTest_transpileToHeader(struct ComStyleAllMethodsTest * this, const char * code) {
}

int TEST_F(struct ComStyleAllMethodsTest, int) {
	const char *code = "\n        class Counter {\n            int value;\n        public:\n            Counter(int v) : value(v) {}\n            int getValue() const { return value; }\n            void increment() { value++; }\n        };\n    ";

	int header;

}

int TEST_F_ComStyleAllMethodsTest_int(struct ComStyleAllMethodsTest, int) {
	const char *code = "\n        class Point {\n            int x, y;\n        public:\n            Point() : x(0), y(0) {}\n            Point(int v) : x(v), y(v) {}\n            Point(int x_, int y_) : x(x_), y(y_) {}\n        };\n    ";

	int header;

}

int TEST_F_ComStyleAllMethodsTest_int_1(struct ComStyleAllMethodsTest, int) {
	const char *code = "\n        class Printer {\n        public:\n            void print(int n) { }\n            void print(double d) { }\n            void print(const char* s) { }\n        };\n    ";

	int header;

}

int TEST_F_ComStyleAllMethodsTest_int_2(struct ComStyleAllMethodsTest, int) {
	const char *code = "\n        class DataHolder {\n            int data;\n        public:\n            int getData() const { return data; }\n            void setData(int d) { data = d; }\n        };\n    ";

	int header;

}

int TEST_F_ComStyleAllMethodsTest_int_3(struct ComStyleAllMethodsTest, int) {
	const char *code = "\n        class Swapper {\n        public:\n            void swap(int& a, int& b) {\n                int temp = a;\n                a = b;\n                b = temp;\n            }\n        };\n    ";

	int header;

}

int TEST_F_ComStyleAllMethodsTest_int_4(struct ComStyleAllMethodsTest, int) {
	const char *code = "\n        class Widget {\n            int value;\n        public:\n            Widget(int v) : value(v) {}\n            int getValue() const { return value; }\n            virtual void update(int v) { value = v; }\n            virtual ~Widget() {}\n        };\n    ";

	int header;

}

int TEST_F_ComStyleAllMethodsTest_int_5(struct ComStyleAllMethodsTest, int) {
	const char *code = "\n        class Empty {\n            // Compiler will generate implicit default ctor, copy ctor, dtor\n        };\n    ";

	int header;

}

int TEST_F_ComStyleAllMethodsTest_int_6(struct ComStyleAllMethodsTest, int) {
	const char *code = "\n        class Resource {\n        public:\n            Resource() {}\n            ~Resource() {}\n        };\n    ";

	int header;

}

