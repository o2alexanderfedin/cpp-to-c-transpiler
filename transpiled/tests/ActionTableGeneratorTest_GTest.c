// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ActionTableGeneratorTest_GTest.cpp
// Implementation file

#include "ActionTableGeneratorTest_GTest.h"

static void TryBlockInfo__ctor_default(struct TryBlockInfo * this) {
	this->tryStmt = 0;
	this->constructedObjects = 0;
	this->tryBlockIndex = 0;
}

static void TryBlockInfo__ctor_copy(struct TryBlockInfo * this, const struct TryBlockInfo * other) {
	this->tryStmt = other->tryStmt;
	this->constructedObjects = other->constructedObjects;
	this->tryBlockIndex = other->tryBlockIndex;
}

static void ActionTableGenerator__ctor_copy(struct ActionTableGenerator * this, const struct ActionTableGenerator * other) {
	this->tryBlocks = other->tryBlocks;
}

int ActionTableGenerator_getTryBlockCount(struct ActionTableGenerator * this) {
}

const int * ActionTableGenerator_getTryBlocks(struct ActionTableGenerator * this) {
}

static void ActionTableGeneratorTestFixture__ctor_default(struct ActionTableGeneratorTestFixture * this) {
}

static void ActionTableGeneratorTestFixture__ctor_copy(struct ActionTableGeneratorTestFixture * this, const struct ActionTableGeneratorTestFixture * other) {
}

int * ActionTableGeneratorTestFixture_findFunction(struct ActionTableGeneratorTestFixture * this, int * TU, const int * name) {
	return nullptr;
;
}

int TEST_F(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        class Resource {\n        public:\n            Resource();\n            ~Resource();\n        };\n\n        void test() {\n            try {\n                Resource r1;\n                Resource r2;\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

}

int TEST_F_ActionTableGeneratorTestFixture_int(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        void test() {\n            try {\n                // Empty\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

}

int TEST_F_ActionTableGeneratorTestFixture_int_1(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        class Resource {\n        public:\n            Resource();\n            ~Resource();\n        };\n\n        void test() {\n            try {\n                Resource r1;\n                Resource r2;\n                Resource r3;\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

	auto destructors = generator()(0);

}

int TEST_F_ActionTableGeneratorTestFixture_int_2(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        class Resource {\n        public:\n            Resource();\n            ~Resource();\n        };\n\n        void test() {\n            try {\n                Resource r1;\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

	int actionTable;

}

int TEST_F_ActionTableGeneratorTestFixture_int_3(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        class Resource {\n        public:\n            Resource();\n            ~Resource();\n        };\n\n        void test() {\n            try {\n                Resource r1;\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

	int actionTable;

}

int TEST_F_ActionTableGeneratorTestFixture_int_4(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        class Resource {\n        public:\n            Resource();\n            ~Resource();\n        };\n\n        void test() {\n            try {\n                Resource r1;\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

	int actionTable;

}

int TEST_F_ActionTableGeneratorTestFixture_int_5(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        class Resource {\n        public:\n            Resource();\n            ~Resource();\n        };\n\n        void test() {\n            try {\n                Resource r1;\n                try {\n                    Resource r2;\n                } catch (...) {}\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

}

int TEST_F_ActionTableGeneratorTestFixture_int_6(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        class Resource {\n        public:\n            Resource();\n            ~Resource();\n        };\n\n        void test() {\n            try {\n                Resource r1;\n                try {\n                    Resource r2;\n                } catch (...) {}\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

	int actionTable0;

	int actionTable1;

}

int TEST_F_ActionTableGeneratorTestFixture_int_7(struct ActionTableGeneratorTestFixture, int) {
	const char *Code = "\n        class Resource {\n        public:\n            Resource();\n            ~Resource();\n        };\n\n        void test() {\n            try {\n                Resource r1;\n            } catch (...) {}\n        }\n    ";

	auto AST;

	auto * TU;
	int *FD;

	struct ActionTableGenerator generator;

	int bindingCode;

}

