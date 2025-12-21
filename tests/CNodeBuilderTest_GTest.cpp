// tests/CNodeBuilderTest_GTest.cpp
// Migrated from CNodeBuilderTest.cpp to Google Test framework
// Story #9: CNodeBuilder structure and type helpers

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "../include/CNodeBuilder.h"

using namespace clang;

// Test fixture for CNodeBuilder tests
class CNodeBuilderTestFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }

    void SetUp() override {
        AST = buildAST("int main() { return 0; }");
        ASSERT_TRUE(AST) << "Failed to create test AST";
    }

    std::unique_ptr<ASTUnit> AST;
};

TEST_F(CNodeBuilderTestFixture, Constructor) {
    ASTContext &Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    // Constructor test - just verify it can be created
    SUCCEED();
}

TEST_F(CNodeBuilderTestFixture, intType) {
    ASTContext &Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    QualType intTy = builder.intType();
    ASSERT_FALSE(intTy.isNull()) << "intType returned null";
    ASSERT_TRUE(intTy->isIntegerType()) << "intType not an integer type";
}

TEST_F(CNodeBuilderTestFixture, voidType) {
    ASTContext &Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    QualType voidTy = builder.voidType();
    ASSERT_FALSE(voidTy.isNull()) << "voidType returned null";
    ASSERT_TRUE(voidTy->isVoidType()) << "voidType not a void type";
}

TEST_F(CNodeBuilderTestFixture, charType) {
    ASTContext &Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    QualType charTy = builder.charType();
    ASSERT_FALSE(charTy.isNull()) << "charType returned null";
    ASSERT_TRUE(charTy->isCharType()) << "charType not a char type";
}

TEST_F(CNodeBuilderTestFixture, ptrType) {
    ASTContext &Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    QualType intTy = builder.intType();
    QualType ptrTy = builder.ptrType(intTy);
    ASSERT_FALSE(ptrTy.isNull()) << "ptrType returned null";
    ASSERT_TRUE(ptrTy->isPointerType()) << "ptrType not a pointer type";
}

TEST_F(CNodeBuilderTestFixture, structType) {
    ASTContext &Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    QualType structTy = builder.structType("Point");
    ASSERT_FALSE(structTy.isNull()) << "structType returned null";
    ASSERT_TRUE(structTy->isStructureType()) << "structType not a structure type";
}
