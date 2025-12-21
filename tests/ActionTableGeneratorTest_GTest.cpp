// tests/ActionTableGeneratorTest_GTest.cpp
// Migrated from ActionTableGeneratorTest.cpp to Google Test framework
// Tests for action table generation (Story #77)

#include <gtest/gtest.h>
#include "ActionTableGenerator.h"
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <memory>
#include <string>

using namespace clang;

// Test fixture for Action Table Generator tests
class ActionTableGeneratorTestFixture : public ::testing::Test {
protected:
    FunctionDecl* findFunction(TranslationUnitDecl *TU, const std::string &name) {
        for (auto *D : TU->decls()) {
            if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
                if (Func->getNameAsString() == name) {
                    return Func;
                }
            }
        }
        return nullptr;
    }
};

// Test Suite: CFG Analysis of Try Blocks (AC #1)

TEST_F(ActionTableGeneratorTestFixture, IdentifyObjectsInTryBlock) {
    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
                Resource r2;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    EXPECT_EQ(generator.getTryBlockCount(), 1u) << "Expected 1 try block";
    EXPECT_EQ(generator.getObjectCount(0), 2u) << "Expected 2 objects in try block";
}

TEST_F(ActionTableGeneratorTestFixture, EmptyTryBlock) {
    const char *Code = R"(
        void test() {
            try {
                // Empty
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    EXPECT_EQ(generator.getTryBlockCount(), 1u) << "Expected 1 try block";
    EXPECT_EQ(generator.getObjectCount(0), 0u) << "Expected 0 objects in try block";
}

// Test Suite: Reverse Ordering (AC #2)

TEST_F(ActionTableGeneratorTestFixture, ReverseDestructorOrder) {
    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
                Resource r2;
                Resource r3;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    auto destructors = generator.getDestructorSequence(0);
    ASSERT_EQ(destructors.size(), 3u) << "Expected 3 destructors";

    EXPECT_NE(destructors[0].find("r3"), std::string::npos) << "First destructor should be r3";
    EXPECT_NE(destructors[1].find("r2"), std::string::npos) << "Second destructor should be r2";
    EXPECT_NE(destructors[2].find("r1"), std::string::npos) << "Third destructor should be r1";
}

// Test Suite: Action Entry Generation (AC #3)

TEST_F(ActionTableGeneratorTestFixture, GenerateActionEntry) {
    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    std::string actionTable = generator.generateActionTable(0);

    EXPECT_NE(actionTable.find("struct __cxx_action_entry"), std::string::npos);
    EXPECT_NE(actionTable.find("actions_try"), std::string::npos);
}

TEST_F(ActionTableGeneratorTestFixture, ActionEntryStructure) {
    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    std::string actionTable = generator.generateActionTable(0);

    EXPECT_NE(actionTable.find("(void(*)(void*))"), std::string::npos);
    EXPECT_NE(actionTable.find("NULL"), std::string::npos);
}

// Test Suite: Sentinel Entry (AC #5)

TEST_F(ActionTableGeneratorTestFixture, SentinelEntry) {
    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    std::string actionTable = generator.generateActionTable(0);

    EXPECT_NE(actionTable.find("{NULL, NULL}"), std::string::npos);
}

// Test Suite: Nested Try Blocks (AC #6)

TEST_F(ActionTableGeneratorTestFixture, NestedTryBlocks) {
    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
                try {
                    Resource r2;
                } catch (...) {}
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    EXPECT_EQ(generator.getTryBlockCount(), 2u) << "Expected 2 try blocks";
    EXPECT_EQ(generator.getObjectCount(0), 1u) << "Outer try should have 1 object";
    EXPECT_EQ(generator.getObjectCount(1), 1u) << "Inner try should have 1 object";
}

TEST_F(ActionTableGeneratorTestFixture, SeparateActionTablesForNestedTry) {
    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
                try {
                    Resource r2;
                } catch (...) {}
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    std::string actionTable0 = generator.generateActionTable(0);
    std::string actionTable1 = generator.generateActionTable(1);

    EXPECT_NE(actionTable0.find("actions_try0"), std::string::npos);
    EXPECT_NE(actionTable1.find("actions_try1"), std::string::npos);
}

// Test Suite: Runtime Address Binding (AC #4)

TEST_F(ActionTableGeneratorTestFixture, RuntimeAddressBinding) {
    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = findFunction(TU, "test");
    ASSERT_NE(FD, nullptr) << "Function 'test' not found";

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    std::string bindingCode = generator.generateRuntimeBinding(0);

    EXPECT_NE(bindingCode.find("actions_try"), std::string::npos);
    EXPECT_NE(bindingCode.find(".object = &"), std::string::npos);
}
