// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/move_semantics/RvalueRefParameterTest.cpp
// Implementation file

#include "RvalueRefParameterTest.h"

static void RvalueRefParamTranslator__ctor_default(struct RvalueRefParamTranslator * this) {
	this->Context = 0;
}

static void RvalueRefParamTranslator__ctor_copy(struct RvalueRefParamTranslator * this, const struct RvalueRefParamTranslator * other) {
	this->Context = other->Context;
}

int buildAST(const char * code) {
}

static void FunctionFinder__ctor_default(struct FunctionFinder * this) {
	this->functions = 0;
	this->rvalueRefParams = 0;
}

static void FunctionFinder__ctor_copy(struct FunctionFinder * this, const struct FunctionFinder * other) {
	this->functions = other->functions;
	this->rvalueRefParams = other->rvalueRefParams;
}

bool FunctionFinder_VisitFunctionDecl(struct FunctionFinder * this, const int * FD) {
	return true;
;
}

static void RvalueRefParameterTest__ctor_default(struct RvalueRefParameterTest * this) {
}

static void RvalueRefParameterTest__ctor_copy(struct RvalueRefParameterTest * this, const struct RvalueRefParameterTest * other) {
}

int TEST_F(struct RvalueRefParameterTest, int) {
	const char *code = "\n            class Buffer {\n                int* data;\n            public:\n                Buffer() : data(nullptr) {}\n            };\n\n            void consume(Buffer&& b) {\n                // Use buffer\n            }\n        ";

	struct FunctionFinder finder;

	const int *Param;

	struct RvalueRefParamTranslator translator;

	int cType;

	int cParam;

}

int TEST_F_RvalueRefParameterTest_int(struct RvalueRefParameterTest, int) {
	const char *code = "\n            class Buffer {\n                int* data;\n            };\n\n            void process(Buffer&& a, Buffer&& b) {\n                // Process both buffers\n            }\n        ";

	struct FunctionFinder finder;

	const int *Func;

	struct RvalueRefParamTranslator translator;

	int cSignature;

	int count;

	int pos;

}

int TEST_F_RvalueRefParameterTest_int_1(struct RvalueRefParameterTest, int) {
	const char *code = "\n            class Buffer {\n                int* data;\n            };\n\n            void mixed(Buffer& lvalue, Buffer&& rvalue, int value) {\n                // Process all parameters\n            }\n        ";

	struct FunctionFinder finder;

	const int *Func;

	struct RvalueRefParamTranslator translator;

	int cSignature;

}

int TEST_F_RvalueRefParameterTest_int_2(struct RvalueRefParameterTest, int) {
	const char *code = "\n            class Buffer {\n                int* data;\n            };\n\n            Buffer global;\n\n            Buffer&& getBuffer() {\n                return static_cast<Buffer&&>(global);\n            }\n        ";

	struct FunctionFinder finder;

	const int *Func;

	struct RvalueRefParamTranslator translator;

	int cSignature;

}

int TEST_F_RvalueRefParameterTest_int_3(struct RvalueRefParameterTest, int) {
	const char *code = "\n            class Buffer {\n                int* data;\n            };\n\n            void readOnly(const Buffer&& b) {\n                // Read from buffer only\n            }\n        ";

	struct FunctionFinder finder;

	const int *Param;

	struct RvalueRefParamTranslator translator;

	int cType;

}

int TEST_F_RvalueRefParameterTest_int_4(struct RvalueRefParameterTest, int) {
	const char *code = "\n            class Buffer {\n                int* data;\n                int size;\n            public:\n                Buffer() : data(nullptr), size(0) {}\n                Buffer(Buffer&& other) : data(other.data), size(other.size) {\n                    other.data = nullptr;\n                    other.size = 0;\n                }\n            };\n\n            void transfer(Buffer&& source, Buffer& dest) {\n                dest = Buffer(static_cast<Buffer&&>(source));\n            }\n        ";

	struct FunctionFinder finder;

	const int *Func;

	struct RvalueRefParamTranslator translator;

	int cSignature;

}

int TEST_F_RvalueRefParameterTest_int_5(struct RvalueRefParameterTest, int) {
	const char *code = "\n            class Buffer {\n                int* data;\n            };\n\n            void consume(Buffer&& b) {\n                // Consume buffer\n            }\n\n            void test() {\n                Buffer b1;\n                consume(static_cast<Buffer&&>(b1));\n            }\n        ";

	struct FunctionFinder finder;

	const int *ConsumeFunc;

	struct RvalueRefParamTranslator translator;

	int cSignature;

}

int TEST_F_RvalueRefParameterTest_int_6(struct RvalueRefParameterTest, int) {
	const char *code = "\n            void processPrimitive(int&& x) {\n                // Process integer\n            }\n        ";

	struct FunctionFinder finder;

	const int *Param;

	struct RvalueRefParamTranslator translator;

	int cParam;

}

int TEST_F_RvalueRefParameterTest_int_7(struct RvalueRefParameterTest, int) {
	const char *code = "\n            template<typename T>\n            void forward(T&& arg) {\n                // Perfect forwarding\n            }\n\n            class Buffer {};\n\n            void test() {\n                Buffer b;\n                forward(b);  // T = Buffer&, not Buffer\n            }\n        ";

}

int TEST_F_RvalueRefParameterTest_int_8(struct RvalueRefParameterTest, int) {
	const char *code = "\n            class Outer {\n            public:\n                class Inner {\n                    int value;\n                };\n\n                void process(Inner&& inner) {\n                    // Process inner object\n                }\n            };\n        ";

	struct FunctionFinder finder;

	const int *Param;

	struct RvalueRefParamTranslator translator;

	int cType;

}

